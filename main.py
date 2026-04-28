from __future__ import annotations

import ast
import csv
import json
import operator
import queue
import re
import threading
import time
import random
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Any, Callable

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

import pyautogui

try:
    import pyperclip
except ImportError:
    pyperclip = None

from transformacoes import TRANSFORMACOES
from dsl_parser import (
    DSL_DEFAULT_SCRIPT,
    FUNC_NAMES as DSL_FUNC_NAMES,
    find_comment_pos,
    is_dsl_content,
    json_to_dsl,
    parse_dsl,
)


class Paths:
    """Application path constants and directory management."""

    APP_DIR = Path(__file__).resolve().parent
    BASE_DIR = APP_DIR.parent
    ROTEIROS_DIR = APP_DIR / "roteiros"
    TABELAS_DIR = APP_DIR / "tabelas"
    HELP_FILE = APP_DIR / "help_roteiro.txt"

    @classmethod
    def ensure_dirs(cls) -> None:
        for folder in (cls.APP_DIR, cls.ROTEIROS_DIR, cls.TABELAS_DIR):
            folder.mkdir(parents=True, exist_ok=True)


Paths.ensure_dirs()
pyautogui.FAILSAFE = True


class Constants:
    """Centralised magic numbers and configuration values."""

    CSV_BUFFER_SIZE: int = 2048
    CLIPBOARD_RETRIES: int = 15
    CLIPBOARD_BASE_DELAY: float = 0.20
    HIGHLIGHT_DEBOUNCE_MS: int = 120
    LOG_POLL_INTERVAL_MS: int = 150
    MOUSE_POLL_INTERVAL_MS: int = 100
    FAILSAFE_CORNER_THRESHOLD: int = 10
    APP_WINDOW_GEOMETRY: str = "1240x800"
    TABLE_EDITOR_GEOMETRY: str = "900x560"
    SCRIPT_EDITOR_GEOMETRY: str = "980x620"
    HELP_WINDOW_GEOMETRY: str = "980x760"


def _parse_script_content(content: str) -> list:
    """Parse roteiro content: DSL or legacy JSON, returning a list of steps."""
    if is_dsl_content(content):
        return parse_dsl(content)
    parsed = json.loads(content)
    if not isinstance(parsed, list):
        raise ValueError("O roteiro deve ser uma lista JSON.")
    return parsed


DEFAULT_SCRIPT = DSL_DEFAULT_SCRIPT


class ConsoleTag(str, Enum):
    """Tags for categorising console log messages by severity and type."""

    DEFAULT = "default"
    INFO = "info"
    SUCCESS = "success"
    WARNING = "warning"
    ERROR = "error"
    STEP = "step"
    ITERATION = "iteration"
    ELAPSED = "elapsed"
    SECTION = "section"


@dataclass
class StepContext:
    """Runtime state carried through a single iteration of script execution."""

    iteration_index: int
    table_contexts: dict[str, "TableCursor"]
    default_table: "TableCursor | None"
    acquired_tables: set[str]
    execution_count: int = 0
    py_result: str = ""


@dataclass
class TableCursor:
    """Manages reading from and writing to a CSV table file, tracking row status."""

    name: str
    path: Path
    rows: list[dict[str, str]]
    fieldnames: list[str]
    pending_indexes: list[int]
    current_index: int | None = None

    @classmethod
    def load(cls, table_name: str) -> "TableCursor":
        path = Paths.TABELAS_DIR / f"{table_name}.csv"
        if not path.exists():
            raise FileNotFoundError(f"Tabela não encontrada: {path.name}")

        with path.open("r", encoding="utf-8-sig", newline="") as file:
            sample = file.read(Constants.CSV_BUFFER_SIZE)
            file.seek(0)
            delimiter = ";" if sample.count(";") >= sample.count(",") else ","
            reader = csv.DictReader(file, delimiter=delimiter)
            rows = [dict(row) for row in reader]
            fieldnames = list(reader.fieldnames or [])

        if "STATUS" not in fieldnames:
            fieldnames.append("STATUS")
            for row in rows:
                row["STATUS"] = row.get("STATUS", "")
        else:
            for row in rows:
                row["STATUS"] = (row.get("STATUS") or "").strip()

        pending_indexes = [
            index
            for index, row in enumerate(rows)
            if (row.get("STATUS") or "").strip().upper() != "OK"
        ]
        return cls(table_name, path, rows, fieldnames, pending_indexes)

    def has_pending(self) -> bool:
        return bool(self.pending_indexes)

    def next_row(self) -> dict[str, str]:
        if not self.pending_indexes:
            raise RuntimeError(f"Tabela {self.name} sem registros pendentes.")
        self.current_index = self.pending_indexes.pop(0)
        return self.rows[self.current_index]

    def get_current_value(self, field: str) -> str:
        if self.current_index is None:
            self.next_row()
        assert self.current_index is not None
        row = self.rows[self.current_index]
        if field not in row:
            raise KeyError(f"Campo {field} não existe na tabela {self.name}.")
        return row.get(field, "") or ""

    def mark_current_ok(self) -> None:
        if self.current_index is None:
            return
        self.rows[self.current_index]["STATUS"] = "OK"

    def reset_current(self) -> None:
        if self.current_index is not None:
            self.pending_indexes.insert(0, self.current_index)
            self.current_index = None

    def save(self) -> None:
        with self.path.open("w", encoding="utf-8", newline="") as file:
            writer = csv.DictWriter(file, fieldnames=self.fieldnames, delimiter=";")
            writer.writeheader()
            writer.writerows(self.rows)


class ScriptRunner:
    """Executes automation scripts step by step, managing table cursors and retries."""

    def __init__(
        self,
        log_callback: Callable[[str, str], None],
        is_stop_requested: Callable[[], bool],
        get_delay: Callable[[], float],
        get_start_delay: Callable[[], float],
    ) -> None:
        self.log = log_callback
        self.is_stop_requested = is_stop_requested
        self.get_delay = get_delay
        self.get_start_delay = get_start_delay

    def run(self, steps: list[dict[str, Any]], repetitions: int, selected_table: str | None, execution_count: int = 0) -> None:
        table_contexts: dict[str, TableCursor] = {}
        default_table = self._load_default_table(selected_table, table_contexts)
        self._load_explicit_tables(steps, table_contexts)
        uses_table = bool(default_table or table_contexts)

        self._apply_initial_delay()

        for iteration_index in range(repetitions):
            if self.is_stop_requested():
                self.log("Execução interrompida pelo usuário.", ConsoleTag.WARNING.value)
                return

            if uses_table and not self._has_rows_available(steps, table_contexts, default_table):
                self.log("Sem registros pendentes suficientes para continuar. Execução finalizada.", ConsoleTag.WARNING.value)
                return

            self._run_iteration(steps, iteration_index, repetitions, table_contexts, default_table, execution_count)

        self.log("Execução concluída.", ConsoleTag.SUCCESS.value)

    def _load_default_table(
        self,
        selected_table: str | None,
        table_contexts: dict[str, TableCursor],
    ) -> TableCursor | None:
        if not selected_table:
            return None
        default_table = TableCursor.load(selected_table)
        table_contexts[selected_table] = default_table
        self.log(
            f"Tabela selecionada: {selected_table} | pendentes: {len(default_table.pending_indexes)}",
            ConsoleTag.INFO.value,
        )
        return default_table

    def _load_explicit_tables(self, steps: list[dict[str, Any]], table_contexts: dict[str, TableCursor]) -> None:
        for table_name in self._extract_explicit_table_names(steps):
            if table_name in table_contexts:
                continue
            table_contexts[table_name] = TableCursor.load(table_name)
            self.log(
                f"Tabela referenciada no roteiro: {table_name} | pendentes: {len(table_contexts[table_name].pending_indexes)}",
                ConsoleTag.INFO.value,
            )

    def _apply_initial_delay(self) -> None:
        start_delay = self.get_start_delay()
        if start_delay > 0:
            self.log(
                f"Delay inicial: aguardando {start_delay} segundo(s) antes de iniciar.",
                ConsoleTag.INFO.value,
            )
            time.sleep(start_delay)

    def _run_iteration(
        self,
        steps: list[dict[str, Any]],
        iteration_index: int,
        repetitions: int,
        table_contexts: dict[str, TableCursor],
        default_table: TableCursor | None,
        execution_count: int = 0,
    ) -> None:
        iteration_start = time.perf_counter()
        acquired_tables: set[str] = set()
        context = StepContext(iteration_index, table_contexts, default_table, acquired_tables, execution_count)

        self.log(f"--- Iteração {iteration_index + 1}/{repetitions} ---", ConsoleTag.ITERATION.value)
        try:
            for step_index, step in enumerate(steps, start=1):
                if self.is_stop_requested():
                    self.log("Execução interrompida pelo usuário.", ConsoleTag.WARNING.value)
                    self._rollback_tables(acquired_tables, table_contexts)
                    return

                self._execute_step(step, step_index, context)
                delay = self.get_delay()
                if delay > 0 and step_index < len(steps):
                    time.sleep(delay)

            self._commit_tables(acquired_tables, table_contexts)
        except Exception as exc:
            self._rollback_tables(acquired_tables, table_contexts)
            raise RuntimeError(f"Erro na iteração {iteration_index + 1}: {exc}") from exc
        finally:
            elapsed = time.perf_counter() - iteration_start
            self.log(f"Tempo total da iteração: {elapsed:.2f}s", ConsoleTag.ELAPSED.value)

    def _commit_tables(self, acquired_tables: set[str], table_contexts: dict[str, TableCursor]) -> None:
        for table_name in acquired_tables:
            cursor = table_contexts[table_name]
            cursor.mark_current_ok()
            cursor.save()
            cursor.current_index = None
            self.log(f"Tabela {table_name}: registro marcado com STATUS=OK", ConsoleTag.SUCCESS.value)

    def _rollback_tables(self, acquired_tables: set[str], table_contexts: dict[str, TableCursor]) -> None:
        for table_name in acquired_tables:
            table_contexts[table_name].reset_current()

    def _execute_step(self, step: dict[str, Any], step_index: int, context: StepContext) -> None:
        secao = step.get("secao")
        if secao is not None:
            self.log(f"{'━' * 6} {secao} {'━' * 6}", ConsoleTag.SECTION.value)
            return

        info = str(step.get("info") or step.get("obs") or f"Item {step_index}")
        before_wait, after_wait = self._parse_wait(step.get("esperar"))
        repeat_count = max(self._parse_repeat(step.get("repetir"), context), 1)
        action_kind, action_payload = self._get_action_payload(step)

        summary = self._build_step_summary(info, action_kind, action_payload, before_wait, after_wait, repeat_count)
        self.log(summary, ConsoleTag.STEP.value)

        for _ in range(repeat_count):
            if before_wait > 0:
                time.sleep(before_wait)

            if action_kind == "mouse":
                self._execute_mouse(action_payload, context)
            elif action_kind == "teclado":
                self._execute_keyboard(action_payload, context)
            elif action_kind == "printscreen":
                self._execute_printscreen(action_payload, context)

            if after_wait > 0:
                time.sleep(after_wait)

    def _get_action_payload(self, step: dict[str, Any]) -> tuple[str | None, dict[str, Any] | None]:
        has_mouse = isinstance(step.get("mouse"), dict) and bool(step.get("mouse"))
        has_keyboard = isinstance(step.get("teclado"), dict) and bool(step.get("teclado"))
        has_printscreen = isinstance(step.get("printscreen"), dict) and bool(step.get("printscreen"))

        action_count = sum(bool(item) for item in (has_mouse, has_keyboard, has_printscreen))
        if action_count > 1:
            raise ValueError("Cada item pode ter somente 1 ação principal: mouse, teclado OU printscreen.")
        if has_mouse:
            return "mouse", step["mouse"]
        if has_keyboard:
            return "teclado", step["teclado"]
        if has_printscreen:
            return "printscreen", step["printscreen"]
        return None, None

    def _build_step_summary(
        self,
        info: str,
        action_kind: str | None,
        action_payload: dict[str, Any] | None,
        before_wait: float,
        after_wait: float,
        repeat_count: int,
    ) -> str:
        parts = [f"> {info}"]
        if before_wait > 0:
            parts.append(f"ANTES={before_wait}s")
        if action_kind == "mouse" and action_payload:
            parts.append(
                f"MOUSE=x:{action_payload.get('x')}, y:{action_payload.get('y')}, acao:{action_payload.get('acao')}"
            )
        elif action_kind == "teclado" and action_payload:
            key, value = next(iter(action_payload.items()))
            parts.append(f"TECLADO={key}:{value}")
        elif action_kind == "printscreen" and action_payload:
            parts.append(
                f"PRINTSCREEN=nome:{action_payload.get('nome_arquivo')}, pasta:{action_payload.get('pasta')}, formato:{action_payload.get('formato', 'png')}"
            )
        if repeat_count > 1:
            parts.append(f"REPETIR={repeat_count}")
        if after_wait > 0:
            parts.append(f"DEPOIS={after_wait}s")
        return " | ".join(parts)

    @staticmethod
    def _iter_step_field_references(steps: list[dict[str, Any]]):
        for step in steps:
            keyboard = step.get("teclado")
            if isinstance(keyboard, dict) and keyboard.get("campo_tabela"):
                yield "campo", str(keyboard["campo_tabela"])
            printscreen = step.get("printscreen")
            if isinstance(printscreen, dict) and printscreen.get("nome_arquivo"):
                yield "template", str(printscreen["nome_arquivo"])

    def _extract_explicit_table_names(self, steps: list[dict[str, Any]]) -> set[str]:
        table_names: set[str] = set()
        for kind, value in self._iter_step_field_references(steps):
            if kind == "campo":
                table_names.update(self._extract_table_names_from_reference(value))
            else:
                table_names.update(self._extract_table_names_from_template(value))
        return table_names

    def _has_rows_available(
        self,
        steps: list[dict[str, Any]],
        table_contexts: dict[str, TableCursor],
        default_table: TableCursor | None,
    ) -> bool:
        for table_name in self._tables_needed_for_iteration(steps, default_table):
            if not table_contexts[table_name].has_pending():
                return False
        return True

    def _tables_needed_for_iteration(self, steps: list[dict[str, Any]], default_table: TableCursor | None) -> set[str]:
        table_names: set[str] = set()
        for kind, value in self._iter_step_field_references(steps):
            if kind == "campo":
                raw = value.strip()
                if "." in raw:
                    table_name, _field = raw.split(".", 1)
                    table_names.add(table_name.strip())
                elif default_table is not None:
                    table_names.add(default_table.name)
            else:
                explicit = self._extract_table_names_from_template(value)
                if explicit:
                    table_names.update(explicit)
                elif self._template_uses_default_table(value) and default_table is not None:
                    table_names.add(default_table.name)
        return table_names

    def _parse_wait(self, wait_value: Any) -> tuple[float, float]:
        before = 0.0
        after = 0.0
        if wait_value in (None, ""):
            return before, after
        if not isinstance(wait_value, dict):
            raise ValueError('Campo "esperar" inválido. Use {"antes": n, "depois": n}.')
        if "antes" in wait_value:
            before = float(wait_value["antes"])
        if "depois" in wait_value:
            after = float(wait_value["depois"])
        return before, after

    def _parse_repeat(self, repeat_value: Any, context: StepContext) -> int:
        if repeat_value in (None, ""):
            return 1
        if isinstance(repeat_value, int):
            return repeat_value
        return int(self._safe_eval(str(repeat_value).strip(), context.iteration_index, context.execution_count))

    def _execute_mouse(self, payload: dict[str, Any], context: StepContext) -> None:
        action = str(payload.get("acao", "")).strip().lower()
        if not action:
            raise ValueError("mouse.acao é obrigatório.")

        x = self._parse_xy_value(payload.get("x"), context)
        y = self._parse_xy_value(payload.get("y"), context)
        self._require_xy(x, y, action)

        if action == "mover":
            pyautogui.moveTo(x, y)
        elif action == "clicar_esquerdo":
            pyautogui.click(x, y, button="left")
        elif action == "clicar_direito":
            pyautogui.click(x, y, button="right")
        elif action == "clicar_duplo":
            pyautogui.doubleClick(x, y, button="left")
        elif action == "clicar_segurar":
            pyautogui.mouseDown(x, y, button="left")
        elif action == "clicar_soltar":
            pyautogui.mouseUp(x, y, button="left")
        else:
            raise ValueError(f"Ação de mouse inválida: {action}")

    def _execute_keyboard(self, payload: dict[str, Any], context: StepContext) -> None:
        allowed_extras = {"colar"}
        action_keys = [k for k in payload if k not in allowed_extras]
        if len(action_keys) != 1:
            raise ValueError("O objeto teclado deve conter somente 1 subitem por passo.")

        action, value = action_keys[0], payload[action_keys[0]]
        action = str(action).strip()

        if action == "digitar":
            text = self._resolve_text_template(str(value), context)
            self._write_text(text)
        elif action == "atalho":
            hotkeys = [part.strip().lower() for part in str(value).split("+") if part.strip()]
            if not hotkeys:
                raise ValueError("Atalho inválido.")
            pyautogui.hotkey(*hotkeys)
        elif action == "pressionar":
            pyautogui.press(str(value).strip().lower())
        elif action == "campo_tabela":
            text = self._resolve_field_reference(str(value).strip(), context)
            self._write_text(text)
        elif action == "funcao_py":
            colar = bool(payload.get("colar", True))
            self._execute_transform_function(str(value).strip(), context, colar)
        elif action == "guardar_py":
            raw = str(value).strip()
            if raw.startswith("[") and raw.endswith("]"):
                raw = raw[1:-1]
            text = self._resolve_field_reference(raw, context)
            context.py_result = text
            self.log(f"guardar_py: {value!r} → {text!r}", ConsoleTag.INFO.value)
        else:
            raise ValueError(
                f"Subitem de teclado inválido: {action}. "
                "Use digitar, atalho, pressionar, campo_tabela, funcao_py ou guardar_py."
            )

    def _execute_printscreen(self, payload: dict[str, Any], context: StepContext) -> None:
        if not isinstance(payload, dict) or not payload:
            raise ValueError("O objeto printscreen deve ser um dicionário válido.")

        output_folder = str(payload.get("pasta") or "").strip()
        if not output_folder:
            raise ValueError("printscreen.pasta é obrigatório.")

        name_template = str(payload.get("nome_arquivo") or "").strip()
        if not name_template:
            raise ValueError("printscreen.nome_arquivo é obrigatório.")

        image_format = str(payload.get("formato") or "png").strip().lower()
        if image_format not in {"png", "jpg", "jpeg", "bmp"}:
            raise ValueError("printscreen.formato inválido. Use png, jpg, jpeg ou bmp.")

        overwrite = bool(payload.get("sobrescrever", False))
        region = self._parse_screenshot_region(payload.get("regiao"), context)
        file_name = self._resolve_filename_template(name_template, context)

        folder_path = Path(output_folder)
        folder_path.mkdir(parents=True, exist_ok=True)

        file_path = folder_path / f"{file_name}.{image_format}"
        if file_path.exists() and not overwrite:
            raise FileExistsError(f"Arquivo já existe e sobrescrever=false: {file_path}")

        screenshot = pyautogui.screenshot(region=region) if region else pyautogui.screenshot()
        save_format = "JPEG" if image_format in {"jpg", "jpeg"} else image_format.upper()
        screenshot.save(file_path, format=save_format)
        self.log(f"Print salvo em: {file_path}", ConsoleTag.SUCCESS.value)

    def _parse_screenshot_region(self, region_value: Any, context: StepContext) -> tuple[int, int, int, int] | None:
        if region_value in (None, ""):
            return None
        if not isinstance(region_value, dict):
            raise ValueError('Campo "printscreen.regiao" inválido. Use {"x": n, "y": n, "largura": n, "altura": n}.')

        required_keys = ("x", "y", "largura", "altura")
        missing = [key for key in required_keys if key not in region_value]
        if missing:
            raise ValueError(f"printscreen.regiao incompleto. Campos obrigatórios: {', '.join(required_keys)}.")

        x = self._parse_xy_value(region_value.get("x"), context)
        y = self._parse_xy_value(region_value.get("y"), context)
        width = self._parse_xy_value(region_value.get("largura"), context)
        height = self._parse_xy_value(region_value.get("altura"), context)
        if width <= 0 or height <= 0:
            raise ValueError("printscreen.regiao exige largura e altura maiores que zero.")
        return (x, y, width, height)

    def _resolve_filename_template(self, template: str, context: StepContext) -> str:
        processed = self._replace_placeholders(template, context)

        def replace_match(match: re.Match[str]) -> str:
            reference = match.group(1).strip()
            if not reference:
                raise ValueError("Placeholder de nome_arquivo vazio. Use [TABELA.CAMPO] ou [CAMPO].")
            return self._resolve_field_reference(reference, context)

        resolved = re.sub(r"\[([^\[\]]+)\]", replace_match, processed)
        sanitized = self._sanitize_file_name(resolved)
        if not sanitized:
            raise ValueError("O nome final do arquivo ficou vazio após sanitização.")
        return sanitized

    @staticmethod
    def _sanitize_file_name(file_name: str) -> str:
        cleaned = re.sub(r'[\/:*?"<>|]+', '_', str(file_name))
        cleaned = re.sub(r'\s+', ' ', cleaned).strip().rstrip('.')
        return cleaned

    @staticmethod
    def _extract_table_names_from_reference(reference: str) -> set[str]:
        raw = str(reference).strip()
        if "." not in raw:
            return set()
        table_name, _field = raw.split(".", 1)
        table_name = table_name.strip()
        return {table_name} if table_name else set()

    def _extract_table_names_from_template(self, template: str) -> set[str]:
        table_names: set[str] = set()
        for match in re.finditer(r"\[([^\[\]]+)\]", str(template)):
            table_names.update(self._extract_table_names_from_reference(match.group(1)))
        return table_names

    @staticmethod
    def _template_uses_default_table(template: str) -> bool:
        for match in re.finditer(r"\[([^\[\]]+)\]", str(template)):
            if "." not in match.group(1).strip():
                return True
        return False

    def _clipboard_op_with_retry(self, op: Callable[[], Any], busy_msg: str, retries: int = Constants.CLIPBOARD_RETRIES, base_delay: float = Constants.CLIPBOARD_BASE_DELAY) -> Any:
        if pyperclip is None:
            raise RuntimeError("pyperclip não está instalado.")
        last_error: Exception | None = None
        for attempt in range(1, retries + 1):
            try:
                return op()
            except Exception as exc:
                last_error = exc
                if attempt < retries:
                    wait_time = base_delay * attempt + random.uniform(0.01, 0.05)
                    self.log(
                        f"{busy_msg} Tentando novamente ({attempt}/{retries}) em {wait_time:.2f}s...",
                        ConsoleTag.WARNING.value,
                    )
                    time.sleep(wait_time)
        raise RuntimeError(f"Falha após {retries} tentativas: {last_error}") from last_error

    def _clipboard_copy_with_retry(self, text: str, retries: int = Constants.CLIPBOARD_RETRIES, base_delay: float = Constants.CLIPBOARD_BASE_DELAY) -> None:
        self._clipboard_op_with_retry(lambda: pyperclip.copy(text), "Clipboard ocupado ao copiar.", retries, base_delay)

    def _clipboard_paste_with_retry(self, retries: int = Constants.CLIPBOARD_RETRIES, base_delay: float = Constants.CLIPBOARD_BASE_DELAY) -> str:
        return self._clipboard_op_with_retry(pyperclip.paste, "Clipboard ocupado ao ler.", retries, base_delay)

    def _paste_via_clipboard(self, text: str) -> None:
        self._clipboard_copy_with_retry(text)
        time.sleep(0.05)
        pyautogui.hotkey("ctrl", "v")

    def _execute_transform_function(self, function_name: str, context: StepContext, colar: bool = True) -> None:
        if pyperclip is None:
            raise RuntimeError("pyperclip não está instalado. Instale para usar funcao_py.")
        function = TRANSFORMACOES.get(function_name)
        if function is None:
            raise KeyError(f"Função não encontrada em TRANSFORMACOES: {function_name}")

        original_text = self._clipboard_paste_with_retry()
        transformed_text = str(function(original_text))
        context.py_result = transformed_text
        self._clipboard_copy_with_retry(transformed_text)
        if colar:
            time.sleep(0.05)
            pyautogui.hotkey("ctrl", "v")
        self.log(f"funcao_py aplicada: {function_name} → {transformed_text!r}  (colar={colar})", ConsoleTag.INFO.value)

    def _write_text(self, text: str) -> None:
        if pyperclip is None:
            pyautogui.write(text, interval=0)
            return

        try:
            self._paste_via_clipboard(text)
        except Exception as exc:
            self.log(
                f"Clipboard indisponível. Usando digitação direta como fallback. Motivo: {exc}",
                ConsoleTag.WARNING.value,
            )
            pyautogui.write(text, interval=0.01)

    def _parse_xy_value(self, value: Any, context: StepContext) -> int:
        if value is None:
            raise ValueError("x e y são obrigatórios para ações de mouse.")
        if isinstance(value, (int, float)):
            return int(value)
        text = self._replace_placeholders(str(value).strip(), context)
        try:
            return int(float(text))
        except ValueError:
            return int(self._safe_eval(text, context.iteration_index, context.execution_count))

    def _resolve_field_reference(self, reference: str, context: StepContext) -> str:
        raw_reference = reference.strip()
        if "." in raw_reference:
            table_name, field_name = raw_reference.split(".", 1)
            table_name = table_name.strip()
            field_name = field_name.strip()
            if table_name not in context.table_contexts:
                context.table_contexts[table_name] = TableCursor.load(table_name)
            cursor = context.table_contexts[table_name]
        else:
            if context.default_table is None:
                raise RuntimeError("campo_tabela sem nome de tabela exige uma tabela selecionada no dropdown.")
            cursor = context.default_table
            field_name = raw_reference

        if cursor.current_index is None:
            cursor.next_row()
            context.acquired_tables.add(cursor.name)
            self.log(f"Tabela {cursor.name}: usando novo registro pendente.", ConsoleTag.INFO.value)

        return cursor.get_current_value(field_name)

    def _replace_placeholders(self, text: str, context: StepContext) -> str:
        return (
            text
            .replace("{i}", str(context.iteration_index))
            .replace("{count}", str(context.execution_count))
            .replace("{py}", context.py_result)
        )

    def _resolve_text_template(self, template: str, context: StepContext) -> str:
        processed = self._replace_placeholders(template, context)

        def replace_match(match: re.Match[str]) -> str:
            reference = match.group(1).strip()
            if not reference:
                raise ValueError("Placeholder de digitar vazio. Use [TABELA.CAMPO] ou [CAMPO].")
            return self._resolve_field_reference(reference, context)

        return re.sub(r"\[([^\[\]]+)\]", replace_match, processed)

    @staticmethod
    def _safe_eval(expression: str, iteration_index: int, execution_count: int = 0) -> int:
        _ALLOWED_OPS: dict[type, Any] = {
            ast.Add: operator.add,
            ast.Sub: operator.sub,
            ast.Mult: operator.mul,
            ast.Div: operator.truediv,
            ast.FloorDiv: operator.floordiv,
            ast.Mod: operator.mod,
            ast.Pow: operator.pow,
        }
        _VARS = {"i": float(iteration_index), "count": float(execution_count)}

        def _eval(node: ast.AST) -> float:
            if isinstance(node, ast.Expression):
                return _eval(node.body)
            if isinstance(node, ast.Constant) and isinstance(node.value, (int, float)):
                return float(node.value)
            if isinstance(node, ast.Name) and node.id in _VARS:
                return _VARS[node.id]
            if isinstance(node, ast.BinOp):
                op_fn = _ALLOWED_OPS.get(type(node.op))
                if op_fn is None:
                    raise ValueError(f"Operação não suportada: {type(node.op).__name__}")
                return op_fn(_eval(node.left), _eval(node.right))
            if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
                return -_eval(node.operand)
            raise ValueError(f"Expressão inválida em 'repetir': {ast.dump(node)}")

        tree = ast.parse(expression.strip(), mode="eval")
        return int(_eval(tree))

    @staticmethod
    def _require_xy(x: Any, y: Any, action: str) -> None:
        if x is None or y is None:
            raise ValueError(f'Ação "{action}" exige x e y no passo do roteiro.')


# ─────────────────────────────────────────────────────────────────────────────
#  DSL Autocomplete
# ─────────────────────────────────────────────────────────────────────────────

class DslAutocomplete:
    """Keyword-aware popup autocomplete for the DSL script editor."""

    _FUNCTIONS = sorted(DSL_FUNC_NAMES)
    _SNIPPETS: dict[str, str] = {
        "esperar":            'esperar(0.5)',
        "mouse":              'mouse(x=, y=, acao="clicar_esquerdo")',
        "printscreen":        ('printscreen(pasta="", nome_arquivo="", formato="png",'
                               ' sobrescrever=false, x=0, y=0, largura=1920, altura=1080)'),
        "secao":              'secao("")',
        "teclado_atalho":     'teclado_atalho("")',
        "teclado_digitar":    'teclado_digitar("")',
        "teclado_funcao_py":  'teclado_funcao_py("", colar=true)',
        "teclado_pressionar": 'teclado_pressionar("")',
    }
    _MOUSE_ACOES  = sorted(["clicar_duplo", "clicar_direito", "clicar_esquerdo",
                             "clicar_segurar", "clicar_soltar", "mover"])
    _FORMATOS     = ["bmp", "jpeg", "jpg", "png"]
    _TECLAS       = sorted(["backspace", "delete", "down", "end", "enter", "esc",
                            "home", "left", "pagedown", "pageup", "right", "space",
                            "tab", "up"] + [f"F{n}" for n in range(1, 13)])
    _TRANSFORM    = sorted(TRANSFORMACOES.keys())

    def __init__(self, editor: tk.Text, get_columns: Callable[[], list[str]]) -> None:
        self._ed = editor
        self._get_cols = get_columns
        self._popup: tk.Toplevel | None = None
        self._lb: tk.Listbox | None = None
        self._items: list[str] = []
        self._ctx: str = "none"
        editor.bind("<KeyRelease>", self._on_key_release, add=True)
        editor.bind("<FocusOut>",   lambda _e: self._hide(), add=True)

    # ── Public ────────────────────────────────────────────────────────────────

    def hide(self) -> None:
        self._hide()

    # ── Context detection ─────────────────────────────────────────────────────

    def _line_to_cursor(self) -> str:
        cursor = self._ed.index("insert")
        row = cursor.split(".")[0]
        return self._ed.get(f"{row}.0", cursor)

    def _get_context(self) -> tuple[str, str]:
        """Return (prefix, context_type)."""
        s = self._line_to_cursor()

        # Inside [CAMPO...]
        m = re.search(r"\[([^\]]*)$", s)
        if m:
            return m.group(1), "bracket"

        # acao="..."
        m = re.search(r'\bacao\s*=\s*"([^"]*)$', s)
        if m:
            return m.group(1), "acao"

        # teclado_funcao_py first quoted arg
        m = re.search(r'\bteclado_funcao_py\s*\(\s*"([^"]*)$', s)
        if m:
            return m.group(1), "funcao_py"

        # teclado_pressionar first quoted arg
        m = re.search(r'\bteclado_pressionar\s*\(\s*"([^"]*)$', s)
        if m:
            return m.group(1), "tecla"

        # formato="..."
        m = re.search(r'\bformato\s*=\s*"([^"]*)$', s)
        if m:
            return m.group(1), "formato"

        # Function name at start of line (no open paren yet)
        if "(" not in s:
            stripped = s.lstrip()
            if re.match(r"^[a-zA-Z_]\w*$", stripped) or stripped == "":
                return stripped, "func"

        return "", "none"

    # ── Update cycle ──────────────────────────────────────────────────────────

    def _on_key_release(self, event: tk.Event) -> None:
        if event.keysym in ("Escape", "Return", "Tab", "Up", "Down", "Left", "Right"):
            return
        prefix, ctx = self._get_context()
        if ctx == "none":
            self._hide()
            return

        if ctx == "func":
            items = [f for f in self._FUNCTIONS if f.startswith(prefix)]
        elif ctx == "acao":
            items = [a for a in self._MOUSE_ACOES if a.startswith(prefix)]
        elif ctx == "funcao_py":
            items = [f for f in self._TRANSFORM if f.startswith(prefix)]
        elif ctx == "tecla":
            items = [t for t in self._TECLAS if t.lower().startswith(prefix.lower())]
        elif ctx == "formato":
            items = [f for f in self._FORMATOS if f.startswith(prefix)]
        elif ctx == "bracket":
            cols = self._get_cols()
            items = [c for c in cols if c.upper().startswith(prefix.upper())]
        else:
            items = []

        if not items:
            self._hide()
            return

        self._ctx = ctx
        self._items = items
        self._show_popup(items)

    # ── Popup ─────────────────────────────────────────────────────────────────

    def _show_popup(self, items: list[str]) -> None:
        if self._popup is None or not self._popup.winfo_exists():
            self._popup = tk.Toplevel(self._ed)
            self._popup.wm_overrideredirect(True)
            self._popup.configure(bg="#1e293b")
            self._lb = tk.Listbox(
                self._popup,
                bg="#1e293b", fg="#e2e8f0",
                selectbackground="#3b82f6", selectforeground="#ffffff",
                font=("Consolas", 10), relief="flat", bd=1,
                activestyle="none", exportselection=False,
            )
            self._lb.pack(fill="both", expand=True)
            self._lb.bind("<ButtonRelease-1>", lambda _e: self._select())
            self._ed.bind("<Down>",   self._on_down)
            self._ed.bind("<Up>",     self._on_up)
            self._ed.bind("<Tab>",    self._on_tab)
            self._ed.bind("<Return>", self._on_return)
            self._ed.bind("<Escape>", lambda _e: self._hide())

        assert self._lb is not None
        self._lb.delete(0, tk.END)
        for item in items:
            self._lb.insert(tk.END, item)
        self._lb.selection_set(0)

        bbox = self._ed.bbox("insert")
        if bbox:
            x = self._ed.winfo_rootx() + bbox[0]
            y = self._ed.winfo_rooty() + bbox[1] + bbox[3]
            w = max(220, max(len(i) for i in items) * 9)
            h = min(len(items), 8) * 19 + 4
            self._popup.geometry(f"{w}x{h}+{x}+{y}")
            self._popup.lift()

    # ── Keyboard handlers (active only while popup is visible) ────────────────

    def _on_down(self, _event: tk.Event) -> str:
        if self._lb:
            sel = self._lb.curselection()
            idx = min((sel[0] if sel else 0) + 1, len(self._items) - 1)
            self._lb.selection_clear(0, tk.END)
            self._lb.selection_set(idx)
            self._lb.see(idx)
        return "break"

    def _on_up(self, _event: tk.Event) -> str:
        if self._lb:
            sel = self._lb.curselection()
            idx = max((sel[0] if sel else 0) - 1, 0)
            self._lb.selection_clear(0, tk.END)
            self._lb.selection_set(idx)
            self._lb.see(idx)
        return "break"

    def _on_tab(self, _event: tk.Event) -> str:
        self._select()
        return "break"

    def _on_return(self, _event: tk.Event) -> str | None:
        if self._lb and self._lb.curselection():
            self._select()
            return "break"
        return None

    # ── Insertion ─────────────────────────────────────────────────────────────

    def _select(self) -> None:
        if self._lb is None:
            return
        sel = self._lb.curselection()
        if not sel:
            return
        chosen = self._items[sel[0]]
        self._do_insert(chosen, self._ctx)
        self._hide()

    def _do_insert(self, chosen: str, ctx: str) -> None:
        cursor = self._ed.index("insert")
        row = cursor.split(".")[0]
        line_start = f"{row}.0"
        line_to_cursor = self._ed.get(line_start, cursor)

        if ctx == "func":
            m = re.search(r"[a-zA-Z_]\w*$", line_to_cursor)
            if m:
                self._ed.delete(f"{row}.{m.start()}", cursor)
            self._ed.insert("insert", self._SNIPPETS.get(chosen, chosen))

        elif ctx in ("acao", "funcao_py", "formato", "tecla"):
            q = line_to_cursor.rfind('"')
            if q >= 0:
                self._ed.delete(f"{row}.{q + 1}", cursor)
            self._ed.insert("insert", chosen)

        elif ctx == "bracket":
            b = line_to_cursor.rfind("[")
            if b >= 0:
                self._ed.delete(f"{row}.{b + 1}", cursor)
            self._ed.insert("insert", chosen + "]")

    # ── Hide ──────────────────────────────────────────────────────────────────

    def _hide(self) -> None:
        if self._popup and self._popup.winfo_exists():
            self._popup.destroy()
        self._popup = None
        self._lb = None
        self._ed.unbind("<Down>")
        self._ed.unbind("<Up>")
        self._ed.unbind("<Tab>")
        self._ed.unbind("<Return>")
        self._ed.unbind("<Escape>")


class BaseEditorWindow(tk.Toplevel):
    """Base class for CRUD editor windows: left file list, right text editor."""

    def __init__(self, master: "AutomationApp", title: str, geometry: str) -> None:
        super().__init__(master)
        self.app = master
        self.title(title)
        self.geometry(geometry)
        self.name_var = tk.StringVar()
        self.listbox: tk.Listbox
        self.editor: tk.Text

    def _get_buttons(self) -> list[tuple[str, Callable]]:
        return []

    def _build_layout(self, name_label: str) -> None:
        left_frame = ttk.Frame(self)
        left_frame.pack(side="left", fill="y", padx=8, pady=8)
        right_frame = ttk.Frame(self)
        right_frame.pack(side="right", fill="both", expand=True, padx=8, pady=8)

        self.listbox = tk.Listbox(left_frame, width=30)
        self.listbox.pack(fill="y", expand=True)
        self.listbox.bind("<<ListboxSelect>>", lambda _event: self.load_selected())

        buttons = ttk.Frame(left_frame)
        buttons.pack(fill="x", pady=(8, 0))
        for text, command in self._get_buttons():
            ttk.Button(buttons, text=text, command=command).pack(fill="x", pady=2)

        top = ttk.Frame(right_frame)
        top.pack(fill="x")
        ttk.Label(top, text=name_label).pack(side="left")
        ttk.Entry(top, textvariable=self.name_var, width=40).pack(side="left", padx=8)

        self.editor = tk.Text(right_frame, wrap="none", undo=True)
        self.editor.pack(fill="both", expand=True, pady=(8, 0))

    def load_selected(self) -> None:
        selection = self.listbox.curselection()
        if not selection:
            return
        name = self.listbox.get(selection[0])
        self.name_var.set(name)
        self.editor.delete("1.0", tk.END)
        self.editor.insert("1.0", self._get_file_path(name).read_text(encoding="utf-8"))

    def _get_file_path(self, name: str) -> Path:
        raise NotImplementedError

    def new_file(self) -> None:
        raise NotImplementedError

    def save_file(self) -> None:
        raise NotImplementedError

    def delete_file(self) -> None:
        raise NotImplementedError

    def refresh_list(self) -> None:
        raise NotImplementedError

    @staticmethod
    def read_file(path: Path) -> str:
        return path.read_text(encoding="utf-8")

    @staticmethod
    def write_file(path: Path, content: str) -> None:
        path.write_text(content, encoding="utf-8")


class TableEditorWindow(BaseEditorWindow):
    def __init__(self, master: "AutomationApp") -> None:
        super().__init__(master, title="CRUD de Tabelas (CSV)", geometry=Constants.TABLE_EDITOR_GEOMETRY)
        self._build_layout("Nome do arquivo (sem .csv):")
        self.editor.insert("1.0", "ID;NOME;STATUS\n1;Exemplo;\n")
        self.refresh_list()

    def _get_buttons(self) -> list[tuple[str, Callable]]:
        return [
            ("Novo", self.new_file),
            ("Importar CSV", self.import_csv),
            ("Salvar", self.save_file),
            ("Excluir", self.delete_file),
            ("Atualizar lista", self.refresh_list),
        ]

    def _get_file_path(self, name: str) -> Path:
        return Paths.TABELAS_DIR / f"{name}.csv"

    def refresh_list(self) -> None:
        self.listbox.delete(0, tk.END)
        for path in sorted(Paths.TABELAS_DIR.glob("*.csv")):
            self.listbox.insert(tk.END, path.stem)

    def new_file(self) -> None:
        self.name_var.set("nova_tabela")
        self.editor.delete("1.0", tk.END)
        self.editor.insert("1.0", "ID;NOME;STATUS\n")

    def import_csv(self) -> None:
        file_path = filedialog.askopenfilename(filetypes=[("CSV", "*.csv"), ("Todos", "*.*")])
        if not file_path:
            return
        source = Path(file_path)
        self.name_var.set(source.stem)
        self.editor.delete("1.0", tk.END)
        self.editor.insert("1.0", source.read_text(encoding="utf-8-sig"))

    def save_file(self) -> None:
        name = self.name_var.get().strip()
        if not name:
            messagebox.showerror("Erro", "Informe o nome do arquivo.")
            return
        path = Paths.TABELAS_DIR / f"{name}.csv"
        content = self.editor.get("1.0", tk.END).strip() + "\n"
        self.write_file(path, content)
        self.app.refresh_table_dropdown()
        self.refresh_list()
        messagebox.showinfo("OK", f"Tabela salva: {path.name}")

    def delete_file(self) -> None:
        name = self.name_var.get().strip()
        if not name:
            return
        path = Paths.TABELAS_DIR / f"{name}.csv"
        if path.exists() and messagebox.askyesno("Confirmar", f"Excluir {path.name}?"):
            path.unlink()
            self.app.refresh_table_dropdown()
            self.refresh_list()
            self.new_file()


class ScriptEditorWindow(BaseEditorWindow):
    def __init__(self, master: "AutomationApp") -> None:
        super().__init__(master, title="CRUD de Roteiros", geometry=Constants.SCRIPT_EDITOR_GEOMETRY)
        self._build_layout("Nome do arquivo (sem .json):")
        self.new_file()
        self.refresh_list()

    def _get_buttons(self) -> list[tuple[str, Callable]]:
        return [
            ("Novo", self.new_file),
            ("Salvar", self.save_file),
            ("Excluir", self.delete_file),
            ("Carregar na tela principal", self.load_into_main),
            ("Converter JSON → DSL", self.convert_to_dsl),
            ("Atualizar lista", self.refresh_list),
        ]

    def _get_file_path(self, name: str) -> Path:
        return Paths.ROTEIROS_DIR / f"{name}.json"

    def refresh_list(self) -> None:
        self.listbox.delete(0, tk.END)
        for path in sorted(Paths.ROTEIROS_DIR.glob("*.json")):
            self.listbox.insert(tk.END, path.stem)
        self.app.refresh_script_dropdown()

    def new_file(self) -> None:
        self.name_var.set("novo_roteiro")
        self.editor.delete("1.0", tk.END)
        self.editor.insert("1.0", DEFAULT_SCRIPT)

    def save_file(self) -> None:
        name = self.name_var.get().strip()
        if not name:
            messagebox.showerror("Erro", "Informe o nome do arquivo.")
            return

        content = self.editor.get("1.0", tk.END).strip()
        try:
            _parse_script_content(content)
        except (json.JSONDecodeError, ValueError) as exc:
            messagebox.showerror("Erro no roteiro", str(exc))
            return

        path = Paths.ROTEIROS_DIR / f"{name}.json"
        self.write_file(path, content)
        self.app.refresh_script_dropdown()
        self.refresh_list()
        messagebox.showinfo("OK", f"Roteiro salvo: {path.name}")

    def delete_file(self) -> None:
        name = self.name_var.get().strip()
        if not name:
            return
        path = Paths.ROTEIROS_DIR / f"{name}.json"
        if path.exists() and messagebox.askyesno("Confirmar", f"Excluir {path.name}?"):
            path.unlink()
            self.app.refresh_script_dropdown()
            self.refresh_list()
            self.new_file()

    def convert_to_dsl(self) -> None:
        content = self.editor.get("1.0", tk.END).strip()
        if not content:
            messagebox.showwarning("Aviso", "Editor vazio.")
            return
        if is_dsl_content(content):
            messagebox.showinfo("Info", "O roteiro já está em formato DSL.")
            return
        try:
            steps = _parse_script_content(content)
            dsl = json_to_dsl(steps)
            self.editor.delete("1.0", tk.END)
            self.editor.insert("1.0", dsl)
        except Exception as exc:
            messagebox.showerror("Erro na conversão", str(exc))

    def load_into_main(self) -> None:
        self.app.script_name_var.set(self.name_var.get().strip())
        self.app.set_script_text(self.editor.get("1.0", tk.END))
        messagebox.showinfo("OK", "Roteiro carregado na tela principal.")


class HelpWindow(tk.Toplevel):
    _BG      = "#0f172a"
    _BG_CODE = "#1a2744"

    _SECTIONS: list[tuple[str, str]] = [
        ("Estrutura",    "sec_estrutura"),
        ("Auxiliares",   "sec_aux"),
        ("Mouse",        "sec_mouse"),
        ("Teclado",      "sec_teclado"),
        ("Printscreen",  "sec_print"),
        ("Placeholders", "sec_ph"),
        ("Tabelas CSV",  "sec_tabelas"),
        ("Exemplos",     "sec_exemplos"),
    ]

    def __init__(self, master: tk.Tk) -> None:
        super().__init__(master)
        self.title("Roterize — Guia de Comandos")
        self.geometry(Constants.HELP_WINDOW_GEOMETRY)
        self.configure(bg=self._BG)
        self.resizable(True, True)
        self._build()

    # ── Layout ────────────────────────────────────────────────────────────────

    def _build(self) -> None:
        # Cabeçalho
        hdr = tk.Frame(self, bg="#1e293b", pady=10)
        hdr.pack(fill="x")
        tk.Label(
            hdr, text="  ROTERIZE  —  Guia de Comandos do Roteiro",
            bg="#1e293b", fg="#f1f5f9", font=("Segoe UI", 13, "bold"),
        ).pack(side="left")

        # Nav bar — botões criados APÓS o conteúdo para ter as posições corretas
        self._nav_frame = tk.Frame(self, bg="#1e293b", pady=5)
        self._nav_frame.pack(fill="x")

        ttk.Separator(self, orient="horizontal").pack(fill="x")

        # Área de conteúdo
        frame = tk.Frame(self, bg=self._BG)
        frame.pack(fill="both", expand=True)

        sb = ttk.Scrollbar(frame)
        sb.pack(side="right", fill="y")

        self._text = tk.Text(
            frame,
            bg=self._BG, fg="#e2e8f0",
            font=("Segoe UI", 10),
            wrap="word", state="normal",
            cursor="arrow",
            padx=28, pady=20,
            spacing1=1, spacing3=3,
            relief="flat",
            yscrollcommand=sb.set,
            selectbackground="#334155",
        )
        self._text.pack(fill="both", expand=True)
        sb.config(command=self._text.yview)

        self._section_positions: dict[str, str] = {}
        self._configure_tags()
        self._build_content()
        self._text.config(state="disabled")

        # Cria botões agora que as posições estão capturadas
        for label, mark in self._SECTIONS:
            idx = self._section_positions.get(mark, "1.0")
            tk.Button(
                self._nav_frame, text=label,
                bg="#334155", fg="#cbd5e1",
                activebackground="#475569", activeforeground="#ffffff",
                relief="flat", padx=10, pady=4,
                font=("Segoe UI", 9), cursor="hand2",
                command=lambda i=idx: self._jump(i),
            ).pack(side="left", padx=(3, 0), pady=2)

    def _jump(self, idx: str) -> None:
        self._text.see(idx)

    # ── Tags ──────────────────────────────────────────────────────────────────

    def _configure_tags(self) -> None:
        t = self._text
        t.tag_configure("h1",     foreground="#fbbf24", font=("Segoe UI", 13, "bold"), spacing1=14, spacing3=4)
        t.tag_configure("h2",     foreground="#93c5fd", font=("Segoe UI", 11, "bold"), spacing1=10, spacing3=2)
        t.tag_configure("h3",     foreground="#6ee7b7", font=("Segoe UI", 10, "bold"), spacing1=6)
        t.tag_configure("body",   foreground="#e2e8f0", font=("Segoe UI", 10))
        t.tag_configure("muted",  foreground="#94a3b8", font=("Segoe UI", 9))
        t.tag_configure("tip",    foreground="#fde68a", font=("Segoe UI", 10))
        t.tag_configure("bullet", foreground="#475569", font=("Segoe UI", 10))
        t.tag_configure("sep",    foreground="#1e3a5f", font=("Consolas", 9),  spacing1=4, spacing3=8)
        t.tag_configure("code",
            foreground="#86efac", font=("Consolas", 10),
            background=self._BG_CODE,
            lmargin1=20, lmargin2=20, spacing1=2, spacing3=2,
        )
        t.tag_configure("inline",  foreground="#86efac", font=("Consolas", 10), background=self._BG_CODE)
        t.tag_configure("field",   foreground="#f9a8d4", font=("Consolas", 10, "bold"))
        t.tag_configure("action",  foreground="#6ee7b7", font=("Consolas", 10, "bold"))
        t.tag_configure("value",   foreground="#fca5a5", font=("Consolas", 10))
        t.tag_configure("ph",      foreground="#fbbf24", font=("Consolas", 10, "bold"), background=self._BG_CODE)
        t.tag_configure("indent",  lmargin1=20, lmargin2=20)
        t.tag_configure("indent2", lmargin1=36, lmargin2=36)

    # ── Helpers de escrita ────────────────────────────────────────────────────

    def _ins(self, text: str, tag: str = "body") -> None:
        self._text.insert(tk.END, text, tag)

    def _nl(self, n: int = 1) -> None:
        self._text.insert(tk.END, "\n" * n)

    def _section(self, label: str, mark: str) -> None:
        self._section_positions[mark] = self._text.index(tk.END)
        self._nl()
        self._ins(f"  {label}\n", "h1")
        self._ins("  " + "─" * 64 + "\n", "sep")

    def _sub(self, title: str) -> None:
        self._nl()
        self._ins(f"  {title}\n", "h2")

    def _sub2(self, title: str) -> None:
        self._nl()
        self._ins(f"    {title}\n", "h3")

    def _item(self, label: str, desc: str, label_tag: str = "field") -> None:
        self._ins("    ")
        self._ins(label, label_tag)
        self._ins(f"  →  {desc}\n", "muted")

    def _code(self, src: str) -> None:
        self._nl()
        for line in src.strip("\n").split("\n"):
            self._ins(f"  {line}\n", "code")
        self._nl()

    def _bullet(self, text: str, tag: str = "body") -> None:
        self._ins("    • ", "bullet")
        self._ins(f"{text}\n", tag)

    def _note(self, text: str) -> None:
        self._ins(f"    ℹ  {text}\n", "muted")

    # ── Conteúdo ──────────────────────────────────────────────────────────────

    def _build_content(self) -> None:
        self._sec_estrutura()
        self._sec_auxiliares()
        self._sec_mouse()
        self._sec_teclado()
        self._sec_printscreen()
        self._sec_variaveis()
        self._sec_tabelas()
        self._sec_exemplos()

    # ── 1. Estrutura ──────────────────────────────────────────────────────────

    def _sec_estrutura(self) -> None:
        self._section("1.  ESTRUTURA GERAL", "sec_estrutura")
        self._nl()
        self._ins("  Um comando por linha. Comentários com ", "body")
        self._ins("--", "field")
        self._ins(". Parâmetros opcionais marcados com ", "body")
        self._ins("?", "tip")
        self._ins(" na documentação — basta omiti-los.\n", "body")
        self._code("""\
-- Variáveis: i (iteração), count (execuções), py (resultado funcao_py)
-- [CAMPO] ou [tabela.CAMPO] = coluna da tabela CSV

secao("Bloco 1 — Abrir janela")

mouse(x=400, y=300, acao="clicar_esquerdo", info="Clicar no campo")
esperar(0.3)

teclado_digitar([NOME], info="Digitar da tabela")

secao("Bloco 2 — Salvar")

teclado_atalho("ctrl+s", info="Salvar")""")
        self._note("Somente um comando por linha. Chamadas longas podem continuar na linha seguinte.")

    # ── 2. Auxiliares ─────────────────────────────────────────────────────────

    def _sec_auxiliares(self) -> None:
        self._section("2.  AUXILIARES", "sec_aux")

        self._sub2("secao(texto)")
        self._ins("  Marcador de bloco. Aparece em ", "body")
        self._ins("amarelo bold", "tip")
        self._ins(" no console. Não executa ação.\n", "body")
        self._code('secao("PARTE 1 — ABRIR VIEW")')

        self._sub2("esperar(segundos)")
        self._ins("  Pausa em segundos.\n", "body")
        self._code("esperar(0.5)   -- aguarda meio segundo\nesperar(1.0)")

        self._sub2("?repetir  e  ?info  em qualquer comando")
        self._ins("  Todo comando de ação aceita ", "body")
        self._ins("repetir", "field")
        self._ins(" e ", "body")
        self._ins("info", "field")
        self._ins(" como parâmetros opcionais.\n", "body")
        self._code("""\
teclado_pressionar("tab", repetir=3, info="Avançar 3 campos")
mouse(x=400, y=300, acao="clicar_esquerdo", repetir=i+1)
teclado_pressionar("tab", repetir=count*2)""")
        self._item("i",     "índice da iteração atual (começa em 0)", "ph")
        self._item("count", "número de execuções acumuladas (começa em 1)", "ph")
        self._note("Operadores disponíveis em repetir:  + − * / // % **")

    # ── 3. Mouse ──────────────────────────────────────────────────────────────

    def _sec_mouse(self) -> None:
        self._section("3.  MOUSE", "sec_mouse")
        self._nl()
        self._ins("  Formato:  ", "muted")
        self._ins("mouse(x=, y=, acao=\"\", ?repetir=1, ?info=\"\")", "inline")
        self._nl(2)
        self._ins("  Ações disponíveis:\n", "body")
        for acao, desc in [
            ("clicar_esquerdo", "clique simples com botão esquerdo"),
            ("clicar_direito",  "clique simples com botão direito"),
            ("clicar_duplo",    "duplo clique com botão esquerdo"),
            ("mover",           "move o cursor sem clicar"),
            ("clicar_segurar",  "pressiona e segura o botão esquerdo"),
            ("clicar_soltar",   "solta o botão esquerdo"),
        ]:
            self._ins("    ")
            self._ins(f"{acao:<20}", "action")
            self._ins(f"→  {desc}\n", "muted")
        self._nl()
        self._ins("  ", "body")
        self._ins("x", "field")
        self._ins(" e ", "body")
        self._ins("y", "field")
        self._ins(" aceitam expressões aritméticas com ", "body")
        self._ins("i", "ph")
        self._ins(" e ", "body")
        self._ins("count", "ph")
        self._ins(":\n", "body")
        self._code("""\
mouse(x=400, y=42 + i * 20, acao="clicar_esquerdo")
-- i=0 → y=42  |  i=1 → y=62  |  i=2 → y=82""")
        self._note("Drag & drop: encadeie clicar_segurar → mover → clicar_soltar.")
        self._code("""\
mouse(x=200, y=300, acao="clicar_segurar")
esperar(0.3)
mouse(x=600, y=300, acao="mover")
esperar(0.1)
mouse(x=600, y=300, acao="clicar_soltar")""")

    # ── 4. Teclado ────────────────────────────────────────────────────────────

    def _sec_teclado(self) -> None:
        self._section("4.  TECLADO", "sec_teclado")

        self._sub2("teclado_digitar(valor, ?variavel_py=false, ?repetir, ?info)")
        self._ins("  Cola texto no campo com foco. ", "body")
        self._ins("valor", "field")
        self._ins(" pode ser string, ", "body")
        self._ins("[CAMPO]", "ph")
        self._ins(" ou variável.\n", "body")
        self._code("""\
teclado_digitar("texto fixo")
teclado_digitar("Arquivo_{i}_exec{count}")  -- placeholders dentro de strings
teclado_digitar([NOME])                     -- coluna da tabela selecionada
teclado_digitar([clientes.EMAIL])           -- coluna de tabela específica
teclado_digitar(py)                         -- último resultado de funcao_py""")
        self._nl()
        self._ins("  Com ", "body")
        self._ins("variavel_py=true", "field")
        self._ins(": lê o valor mas ", "body")
        self._ins("não digita", "tip")
        self._ins(", armazena em ", "body")
        self._ins("py", "ph")
        self._ins(":\n", "body")
        self._code("""\
teclado_digitar([NOME], variavel_py=true)   -- guarda em py sem digitar
teclado_funcao_py("upper", colar=true)      -- aplica upper sobre py, digita""")

        self._sub2("teclado_atalho(teclas, ?repetir, ?info)")
        self._ins("  Executa uma combinação de teclas (hotkey).\n", "body")
        self._code("""\
teclado_atalho("ctrl+s")
teclado_atalho("ctrl+shift+a")
teclado_atalho("alt+f4")""")

        self._sub2("teclado_pressionar(tecla, ?repetir, ?info)")
        self._ins("  Pressiona uma única tecla.\n", "body")
        self._code('teclado_pressionar("enter")\nteclado_pressionar("tab", repetir=3)')
        self._nl()
        self._ins("  Teclas comuns: ", "muted")
        self._ins(
            "enter  tab  esc  space  backspace  delete  up  down  left  right  home  end  pageup  pagedown  F1…F12\n",
            "inline",
        )

        self._sub2("teclado_funcao_py(funcao, colar, ?repetir, ?info)")
        self._ins("  Aplica uma função de ", "body")
        self._ins("transformacoes.py", "field")
        self._ins(" sobre o texto no clipboard. ", "body")
        self._ins("colar=true", "field")
        self._ins(" cola o resultado; ", "body")
        self._ins("colar=false", "field")
        self._ins(" armazena em ", "body")
        self._ins("py", "ph")
        self._ins(".\n", "body")
        self._code("""\
teclado_atalho("ctrl+c")
esperar(0.3)
teclado_funcao_py("upper", colar=true)

-- Encadeamento via py:
teclado_funcao_py("extrair_tabela_do_from", colar=false)  -- clipboard → py
teclado_funcao_py("trocar_prefixo_tabela_rf", colar=true) -- py → digita""")
        self._nl()
        self._ins("  Funções disponíveis em transformacoes.py:\n", "muted")
        for fn in sorted(TRANSFORMACOES.keys()):
            self._ins(f"    {fn}\n", "inline")

    # ── 5. Printscreen ────────────────────────────────────────────────────────

    def _sec_printscreen(self) -> None:
        self._section("5.  PRINTSCREEN", "sec_print")
        self._nl()
        self._ins("  Todos os parâmetros são ", "body")
        self._ins("obrigatórios", "tip")
        self._ins(":\n", "body")
        self._code("""\
printscreen(pasta="C:/prints",
            nome_arquivo="Print_{count}_{i}_[CAMPO]",
            formato="png",
            sobrescrever=false,
            x=0, y=0, largura=1920, altura=1080)""")
        self._nl()
        for campo, desc in [
            ("pasta",        "caminho da pasta de destino (criada automaticamente se não existir)"),
            ("nome_arquivo", "nome do arquivo sem extensão — aceita [CAMPO] e {placeholders}"),
            ("formato",      "png  |  jpg  |  jpeg  |  bmp"),
            ("sobrescrever", "true = substitui arquivo existente, false = erro se já existir"),
            ("x, y",         "coordenada superior esquerda da região capturada"),
            ("largura, altura", "dimensões da região capturada em pixels"),
        ]:
            self._ins("    ")
            self._ins(f"{campo:<20}", "field")
            self._ins(f"{desc}\n", "muted")
        self._nl()
        self._ins("  Valores dinâmicos em ", "body")
        self._ins("nome_arquivo", "field")
        self._ins(":\n", "body")
        for token, desc in [
            ("[CAMPO]",        "coluna da tabela selecionada no dropdown"),
            ("[tabela.CAMPO]", "coluna de tabela específica"),
            ("{count}",        "número de execuções acumuladas"),
            ("{i}",            "índice da iteração atual"),
            ("{py}",           "último resultado de funcao_py"),
        ]:
            self._ins("    ")
            self._ins(f"{token:<22}", "ph")
            self._ins(f"→  {desc}\n", "muted")
        self._code('printscreen(pasta="C:/prints", nome_arquivo="Rel_[clientes.NOME]_exec{count}_iter{i}",\n'
                   '            formato="png", sobrescrever=false, x=0, y=0, largura=1920, altura=1080)')

    # ── 6. Variáveis e placeholders ───────────────────────────────────────────

    def _sec_variaveis(self) -> None:
        self._section("6.  VARIÁVEIS E PLACEHOLDERS", "sec_ph")
        self._nl()
        self._ins("  Variáveis disponíveis como argumentos diretos ou ", "body")
        self._ins("{placeholder}", "ph")
        self._ins(" dentro de strings:\n", "body")
        self._nl()
        for var, ph, desc in [
            ("i",     "{i}",     "índice da iteração atual (começa em 0, reseta a cada Executar)"),
            ("count", "{count}", "total de cliques em Executar na sessão (começa em 1, acumula)"),
            ("py",    "{py}",    "último resultado de funcao_py com colar=false (reseta a cada iteração)"),
        ]:
            self._ins(f"    ")
            self._ins(f"{var:<8}", "ph")
            self._ins(f"ou  ", "muted")
            self._ins(f"{ph:<10}", "ph")
            self._ins(f"{desc}\n", "body")
        self._nl()
        self._code("""\
teclado_digitar("Arquivo_{count}_linha_{i}")
teclado_digitar([NOME])                          -- coluna da tabela
mouse(x=400, y=42 + i * 20, acao="clicar_esquerdo")
teclado_pressionar("tab", repetir=count + i)
printscreen(pasta="C:/p", nome_arquivo="Print_{count}_{i}_[CAMPO]",
            formato="png", sobrescrever=false, x=0, y=0, largura=1920, altura=1080)""")

    # ── 7. Tabelas CSV ────────────────────────────────────────────────────────

    def _sec_tabelas(self) -> None:
        self._section("7.  TABELAS CSV", "sec_tabelas")
        self._nl()
        self._bullet("Separador preferencial: ponto e vírgula  ( ; )")
        self._bullet("Deve ter cabeçalho na primeira linha")
        self._bullet("A coluna STATUS é gerenciada automaticamente pelo app")
        self._nl()
        self._code("""\
ID;NOME;EMAIL;STATUS
1;João Silva;joao@email.com;OK
2;Maria Santos;maria@email.com;
3;Pedro Alves;pedro@email.com;""")
        self._ins("  Comportamento da coluna STATUS:\n", "h3")
        self._item("(vazio)", "registro pendente — será processado na próxima execução", "value")
        self._item("OK",      "registro já processado — ignorado nas próximas execuções", "action")
        self._note("Rollback automático: se a iteração falhar ou for interrompida, o STATUS não é gravado.")
        self._nl()
        self._ins("  Referência a tabelas no roteiro:\n", "body")
        self._code("""\
teclado_digitar([NOME])            -- tabela selecionada no dropdown
teclado_digitar([clientes.EMAIL])  -- tabela específica
teclado_digitar([NOME], variavel_py=true)  -- lê sem digitar, guarda em py""")
        self._bullet("Ao concluir a iteração com sucesso  →  STATUS = OK na linha usada")
        self._bullet("Se houver erro ou interrupção  →  rollback automático")
        self._bullet("É possível usar mais de uma tabela no mesmo roteiro")

    # ── 8. Exemplos ───────────────────────────────────────────────────────────

    def _sec_exemplos(self) -> None:
        self._section("8.  EXEMPLOS COMPLETOS", "sec_exemplos")

        self._sub("8.1  Fluxo básico com tabela")
        self._code("""\
secao("PREENCHER FORMULÁRIO")

mouse(x=400, y=300, acao="clicar_esquerdo", info="Clicar no campo nome")
teclado_digitar([NOME], info="Digitar nome da tabela")
teclado_pressionar("tab")
teclado_atalho("ctrl+s", info="Salvar registro")
esperar(1.0)""")

        self._sub("8.2  Print com nome dinâmico")
        self._code("""\
secao("CAPTURAR TELA")

esperar(2.0)
printscreen(pasta="C:/prints/exec_{count}",
            nome_arquivo="[tabela.CODIGO]_iter{i}",
            formato="png", sobrescrever=true,
            x=0, y=0, largura=1920, altura=1040)""")

        self._sub("8.3  Drag and drop")
        self._code("""\
secao("ARRASTAR ELEMENTO")

mouse(x=200, y=300, acao="clicar_segurar", info="Segurar item")
esperar(0.3)
mouse(x=600, y=300, acao="mover", info="Mover para destino")
esperar(0.1)
mouse(x=600, y=300, acao="clicar_soltar", info="Soltar item")
esperar(1.5)""")

        self._sub("8.4  Encadeamento de funcao_py via py")
        self._code("""\
secao("TRANSFORMAR E DIGITAR")

teclado_atalho("ctrl+c")
esperar(0.3)
teclado_funcao_py("extrair_tabela_do_from", colar=false)  -- clipboard → py
teclado_funcao_py("trocar_prefixo_tabela_rf", colar=true) -- py → digita""")

        self._sub("8.5  Múltiplas tabelas")
        self._code("""\
secao("CADASTRO COM DUAS TABELAS")

teclado_digitar([tabela_a.NOME], info="Campo A")
teclado_digitar([tabela_b.CODIGO], info="Campo B")
teclado_pressionar("enter")
esperar(0.5)""")
        self._nl(3)


class AutomationApp(tk.Tk):
    """Main application window for the Roterize automation tool."""

    def __init__(self) -> None:
        super().__init__()
        self.title("Roterize")
        self.geometry(Constants.APP_WINDOW_GEOMETRY)

        self.script_name_var = tk.StringVar()
        self.selected_table_var = tk.StringVar()
        self.start_delay_var = tk.StringVar(value="0")
        self.delay_var = tk.StringVar(value="0.3")
        self.repetitions_var = tk.StringVar(value="1")
        self.mouse_position_var = tk.StringVar(value="Mouse: X=0  Y=0")
        self.execution_count: int = 0
        self.count_var = tk.StringVar(value="Count: 0")

        self.log_queue: queue.Queue[tuple[str, str]] = queue.Queue()
        self.stop_event = threading.Event()
        self.worker_thread: threading.Thread | None = None
        self._highlight_after_id: str | None = None
        self._last_line_count: int = 0

        self.script_text: tk.Text
        self.line_numbers: tk.Text
        self.script_scrollbar: ttk.Scrollbar
        self.console_text: tk.Text
        self.script_combo: ttk.Combobox
        self.table_combo: ttk.Combobox

        self._build_ui()
        self.refresh_script_dropdown()
        self.refresh_table_dropdown()
        self.set_script_text(DEFAULT_SCRIPT)
        self.after(Constants.LOG_POLL_INTERVAL_MS, self.process_log_queue)
        self.after(Constants.MOUSE_POLL_INTERVAL_MS, self.update_mouse_position)

    def _build_ui(self) -> None:
        # ── Menu bar ──────────────────────────────────────────────────────────
        menubar = tk.Menu(self)
        cadastros_menu = tk.Menu(menubar, tearoff=0)
        cadastros_menu.add_command(label="Roteiros", command=self.open_script_editor)
        cadastros_menu.add_command(label="Tabelas", command=self.open_table_editor)
        menubar.add_cascade(label="Cadastros", menu=cadastros_menu)
        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="Comandos do Roteiro", command=self.open_help)
        menubar.add_cascade(label="Help", menu=help_menu)
        self.config(menu=menubar)

        # ── Toolbar ───────────────────────────────────────────────────────────
        toolbar = ttk.Frame(self, padding=(10, 8, 10, 4))
        toolbar.pack(fill="x")

        roteiro_lf = ttk.LabelFrame(toolbar, text="Roteiro", padding=6)
        roteiro_lf.pack(side="left", fill="both", expand=True, padx=(0, 6))

        row0 = ttk.Frame(roteiro_lf)
        row0.pack(fill="x")
        ttk.Label(row0, text="Roteiro:").pack(side="left")
        self.script_combo = ttk.Combobox(row0, textvariable=self.script_name_var, width=30)
        self.script_combo.pack(side="left", padx=(4, 2))
        self.script_combo.bind("<<ComboboxSelected>>", lambda _e: self.load_selected_script())
        ttk.Button(row0, text="Salvar", command=self.save_script_from_main).pack(side="left", padx=2)
        ttk.Button(row0, text="JSON → DSL", command=self.convert_to_dsl).pack(side="left", padx=(8, 2))

        exec_lf = ttk.LabelFrame(toolbar, text="Execução", padding=6)
        exec_lf.pack(side="left", fill="y", padx=(6, 0))

        ttk.Label(exec_lf, text="Tabela:").grid(row=0, column=0, sticky="e", padx=(0, 4), pady=2)
        self.table_combo = ttk.Combobox(exec_lf, textvariable=self.selected_table_var, state="readonly", width=22)
        self.table_combo.grid(row=0, column=1, columnspan=3, sticky="we", pady=2)

        ttk.Label(exec_lf, text="Delay inicial (s):").grid(row=1, column=0, sticky="e", padx=(0, 4), pady=2)
        ttk.Entry(exec_lf, textvariable=self.start_delay_var, width=7).grid(row=1, column=1, sticky="w", pady=2)
        ttk.Label(exec_lf, text="Delay passos (s):").grid(row=1, column=2, sticky="e", padx=(10, 4), pady=2)
        ttk.Entry(exec_lf, textvariable=self.delay_var, width=7).grid(row=1, column=3, sticky="w", pady=2)

        ttk.Label(exec_lf, text="Repetições:").grid(row=2, column=0, sticky="e", padx=(0, 4), pady=2)
        ttk.Entry(exec_lf, textvariable=self.repetitions_var, width=7).grid(row=2, column=1, sticky="w", pady=2)

        # ── Barra de controles ────────────────────────────────────────────────
        controls = ttk.Frame(self, padding=(10, 4, 10, 6))
        controls.pack(fill="x")

        tk.Button(
            controls, text="▶  EXECUTAR", command=self.start_execution,
            bg="#16a34a", fg="white", activebackground="#15803d", activeforeground="white",
            font=("Segoe UI", 10, "bold"), relief="flat", padx=14, pady=5, cursor="hand2",
        ).pack(side="left", padx=(0, 6))

        tk.Button(
            controls, text="■  PARAR", command=self.stop_execution,
            bg="#dc2626", fg="white", activebackground="#b91c1c", activeforeground="white",
            font=("Segoe UI", 10, "bold"), relief="flat", padx=14, pady=5, cursor="hand2",
        ).pack(side="left", padx=(0, 10))

        ttk.Separator(controls, orient="vertical").pack(side="left", fill="y", padx=8)
        ttk.Label(controls, textvariable=self.mouse_position_var, font=("Consolas", 11)).pack(side="left", padx=(0, 16))
        ttk.Label(controls, textvariable=self.count_var, font=("Consolas", 11)).pack(side="left")

        # ── Editor + Console ──────────────────────────────────────────────────
        center = ttk.Panedwindow(self, orient="vertical")
        center.pack(fill="both", expand=True, padx=10, pady=(0, 10))

        script_frame = ttk.Labelframe(center, text="Roteiro para execução")
        console_frame = ttk.Labelframe(center, text="Console")
        center.add(script_frame, weight=3)
        center.add(console_frame, weight=2)

        self._build_script_editor(script_frame)
        self._build_console(console_frame)

    def _build_console(self, console_frame: ttk.Labelframe) -> None:
        header = ttk.Frame(console_frame)
        header.pack(fill="x", padx=6, pady=(4, 0))
        ttk.Button(header, text="Limpar console", command=self.clear_console).pack(side="right")

        self.console_text = tk.Text(
            console_frame,
            wrap="word",
            state="disabled",
            height=12,
            bg="#111827",
            fg="#e5e7eb",
            insertbackground="#ffffff",
            padx=8,
            pady=8,
            font=("Consolas", 10),
        )
        self.console_text.pack(fill="both", expand=True, padx=6, pady=(4, 6))
        self._configure_console_tags()

    def _build_script_editor(self, script_frame: ttk.Labelframe) -> None:
        script_container = ttk.Frame(script_frame)
        script_container.pack(fill="both", expand=True, padx=6, pady=6)

        self.line_numbers = tk.Text(
            script_container,
            width=5,
            padx=4,
            takefocus=0,
            border=0,
            background="#111827",
            foreground="#94a3b8",
            state="disabled",
            wrap="none",
            font=("Consolas", 10),
        )
        self.line_numbers.pack(side="left", fill="y")

        self.script_scrollbar = ttk.Scrollbar(script_container)
        self.script_scrollbar.pack(side="right", fill="y")

        self.script_text = tk.Text(
            script_container,
            wrap="none",
            undo=True,
            height=20,
            bg="#0f172a",
            fg="#e2e8f0",
            insertbackground="#f8fafc",
            selectbackground="#334155",
            padx=10,
            pady=10,
            font=("Consolas", 10),
            yscrollcommand=self._on_script_scroll,
        )
        self.script_text.pack(side="left", fill="both", expand=True)
        self.script_scrollbar.config(command=self._sync_scroll)

        self._configure_script_tags()
        self.script_text.bind("<KeyRelease>", self._handle_script_change)
        self.script_text.bind("<<Paste>>", lambda _event: self.after(10, self._refresh_script_view))
        self.script_text.bind("<MouseWheel>", lambda _event: self.after(10, self._update_line_numbers))
        self.script_text.bind("<Button-4>", lambda _event: self.after(10, self._update_line_numbers))
        self.script_text.bind("<Button-5>", lambda _event: self.after(10, self._update_line_numbers))
        self._autocomplete = DslAutocomplete(self.script_text, self.get_table_columns)

    def _configure_script_tags(self) -> None:
        t = self.script_text
        t.tag_configure("dsl_func",    foreground="#60a5fa", font=("Consolas", 10, "bold"))
        t.tag_configure("dsl_string",  foreground="#86efac")
        t.tag_configure("dsl_bracket", foreground="#fb923c", font=("Consolas", 10, "bold"))
        t.tag_configure("dsl_comment", foreground="#4b5563", font=("Consolas", 10, "italic"))
        t.tag_configure("dsl_number",  foreground="#fca5a5")
        t.tag_configure("dsl_bool",    foreground="#c4b5fd")
        t.tag_configure("dsl_var",     foreground="#fbbf24")
        t.tag_configure("dsl_param",   foreground="#67e8f9")

    def _configure_console_tags(self) -> None:
        self.console_text.tag_configure(ConsoleTag.DEFAULT.value, foreground="#e5e7eb")
        self.console_text.tag_configure(ConsoleTag.INFO.value, foreground="#93c5fd")
        self.console_text.tag_configure(ConsoleTag.SUCCESS.value, foreground="#86efac")
        self.console_text.tag_configure(ConsoleTag.WARNING.value, foreground="#fde68a")
        self.console_text.tag_configure(ConsoleTag.ERROR.value, foreground="#fca5a5")
        self.console_text.tag_configure(ConsoleTag.STEP.value, foreground="#e5e7eb")
        self.console_text.tag_configure(ConsoleTag.ITERATION.value, foreground="#ffffff", font=("Consolas", 10, "bold"))
        self.console_text.tag_configure(ConsoleTag.ELAPSED.value, foreground="#ff6b6b")
        self.console_text.tag_configure(ConsoleTag.SECTION.value, foreground="#fbbf24", font=("Consolas", 10, "bold"))

    def set_script_text(self, content: str) -> None:
        self.script_text.delete("1.0", tk.END)
        self.script_text.insert("1.0", content.rstrip() + "\n")
        self._refresh_script_view()

    def _handle_script_change(self, _event: tk.Event) -> None:
        if self._highlight_after_id:
            self.after_cancel(self._highlight_after_id)
        self._highlight_after_id = self.after(Constants.HIGHLIGHT_DEBOUNCE_MS, self._refresh_script_view)

    def _refresh_script_view(self) -> None:
        self._apply_dsl_highlight()
        self._update_line_numbers()

    def _update_line_numbers(self) -> None:
        content = self.script_text.get("1.0", "end-1c")
        line_count = max(1, content.count("\n") + 1)
        if line_count != self._last_line_count:
            self._last_line_count = line_count
            numbers = "\n".join(str(i) for i in range(1, line_count + 1))
            self.line_numbers.config(state="normal")
            self.line_numbers.delete("1.0", tk.END)
            self.line_numbers.insert("1.0", numbers)
            self.line_numbers.config(state="disabled")
        self.line_numbers.yview_moveto(self.script_text.yview()[0])

    def _on_script_scroll(self, first: str, last: str) -> None:
        self.script_scrollbar.set(first, last)
        self.line_numbers.yview_moveto(float(first))

    def _sync_scroll(self, *args: Any) -> None:
        self.script_text.yview(*args)
        self.line_numbers.yview(*args)

    _DSL_TAGS = ("dsl_func", "dsl_string", "dsl_bracket", "dsl_comment",
                 "dsl_number", "dsl_bool", "dsl_var", "dsl_param")
    _DSL_FUNC_RE = re.compile(
        r"\b(" + "|".join(sorted(DSL_FUNC_NAMES, key=len, reverse=True)) + r")\b"
    )
    _DSL_PARAM_RE  = re.compile(r"\b([a-zA-Z_]\w*)\s*(?==)")
    _DSL_STRING_RE = re.compile(r'"[^"]*"')
    _DSL_BRACKET_RE = re.compile(r"\[[^\[\]]+\]")
    _DSL_NUMBER_RE = re.compile(r"(?<!['\w])-?\b\d+(?:\.\d+)?\b")
    _DSL_BOOL_RE   = re.compile(r"\b(true|false)\b")
    _DSL_VAR_RE    = re.compile(r"\b(i|count|py)\b")

    def _apply_dsl_highlight(self) -> None:
        content = self.script_text.get("1.0", "end-1c")

        # Legacy JSON: fall back to minimal brace/string colouring
        if not is_dsl_content(content):
            for tag in self._DSL_TAGS:
                self.script_text.tag_remove(tag, "1.0", tk.END)
            for m in re.finditer(r'"[^"]*"', content):
                self.script_text.tag_add("dsl_string", f"1.0+{m.start()}c", f"1.0+{m.end()}c")
            return

        for tag in self._DSL_TAGS:
            self.script_text.tag_remove(tag, "1.0", tk.END)

        def _tag(tag: str, start: int, end: int) -> None:
            self.script_text.tag_add(tag, f"1.0+{start}c", f"1.0+{end}c")

        # Process line by line to properly handle comments and string ranges
        offset = 0
        for line in content.split("\n"):
            comment_pos = find_comment_pos(line)
            code = line[:comment_pos] if comment_pos >= 0 else line

            # Collect string ranges so other patterns skip inside them
            string_ranges: list[tuple[int, int]] = []
            for m in self._DSL_STRING_RE.finditer(code):
                string_ranges.append((m.start(), m.end()))
                _tag("dsl_string", offset + m.start(), offset + m.end())

            def _outside_strings(start: int, end: int) -> bool:
                return not any(s <= start < e for s, e in string_ranges)

            for m in self._DSL_FUNC_RE.finditer(code):
                if _outside_strings(m.start(), m.end()):
                    _tag("dsl_func", offset + m.start(), offset + m.end())

            for m in self._DSL_PARAM_RE.finditer(code):
                if _outside_strings(m.start(), m.end()):
                    _tag("dsl_param", offset + m.start(), offset + m.end())

            for m in self._DSL_BRACKET_RE.finditer(code):
                if _outside_strings(m.start(), m.end()):
                    _tag("dsl_bracket", offset + m.start(), offset + m.end())

            for m in self._DSL_NUMBER_RE.finditer(code):
                if _outside_strings(m.start(), m.end()):
                    _tag("dsl_number", offset + m.start(), offset + m.end())

            for m in self._DSL_BOOL_RE.finditer(code):
                if _outside_strings(m.start(), m.end()):
                    _tag("dsl_bool", offset + m.start(), offset + m.end())

            for m in self._DSL_VAR_RE.finditer(code):
                if _outside_strings(m.start(), m.end()):
                    _tag("dsl_var", offset + m.start(), offset + m.end())

            if comment_pos >= 0:
                _tag("dsl_comment", offset + comment_pos, offset + len(line))

            offset += len(line) + 1  # +1 for \n

    def _refresh_dropdown(self, combo: ttk.Combobox, var: tk.StringVar, directory: Path, pattern: str) -> None:
        values = [""] + [path.stem for path in sorted(directory.glob(pattern))]
        combo["values"] = values
        if var.get() not in values:
            var.set("")

    def refresh_script_dropdown(self) -> None:
        self._refresh_dropdown(self.script_combo, self.script_name_var, Paths.ROTEIROS_DIR, "*.json")

    def refresh_table_dropdown(self) -> None:
        self._refresh_dropdown(self.table_combo, self.selected_table_var, Paths.TABELAS_DIR, "*.csv")

    def get_table_columns(self) -> list[str]:
        name = self.selected_table_var.get().strip()
        if not name:
            return []
        path = Paths.TABELAS_DIR / f"{name}.csv"
        if not path.exists():
            return []
        try:
            with path.open("r", encoding="utf-8-sig", newline="") as fh:
                sample = fh.read(Constants.CSV_BUFFER_SIZE)
                fh.seek(0)
                delim = ";" if sample.count(";") >= sample.count(",") else ","
                reader = csv.DictReader(fh, delimiter=delim)
                next(reader, None)
                return [c for c in (reader.fieldnames or []) if c != "STATUS"]
        except Exception:
            return []

    def open_help(self) -> None:
        HelpWindow(self)

    def open_table_editor(self) -> None:
        TableEditorWindow(self)

    def open_script_editor(self) -> None:
        ScriptEditorWindow(self)

    def load_selected_script(self) -> None:
        name = self.script_name_var.get().strip()
        if not name:
            return
        path = Paths.ROTEIROS_DIR / f"{name}.json"
        if not path.exists():
            messagebox.showerror("Erro", "Roteiro não encontrado.")
            return
        self.set_script_text(path.read_text(encoding="utf-8"))
        self.log(f"Roteiro carregado: {name}", ConsoleTag.INFO.value)

    def save_script_from_main(self) -> None:
        name = self.script_name_var.get().strip() or "roteiro_principal"
        content = self.script_text.get("1.0", tk.END).strip()
        try:
            _parse_script_content(content)
        except (json.JSONDecodeError, ValueError) as exc:
            messagebox.showerror("Erro no roteiro", str(exc))
            return

        path = Paths.ROTEIROS_DIR / f"{name}.json"
        path.write_text(content, encoding="utf-8")
        self.refresh_script_dropdown()
        self.script_name_var.set(name)
        self.log(f"Roteiro salvo: {path.name}", ConsoleTag.SUCCESS.value)
        messagebox.showinfo("OK", f"Roteiro salvo: {path.name}")

    def convert_to_dsl(self) -> None:
        content = self.script_text.get("1.0", tk.END).strip()
        if not content:
            messagebox.showwarning("Aviso", "Editor vazio.")
            return
        if is_dsl_content(content):
            messagebox.showinfo("Info", "O roteiro já está em formato DSL.")
            return
        try:
            steps = _parse_script_content(content)
            self.set_script_text(json_to_dsl(steps))
            self.log("Roteiro convertido para DSL.", ConsoleTag.SUCCESS.value)
        except Exception as exc:
            messagebox.showerror("Erro na conversão", str(exc))

    def start_execution(self) -> None:
        if self.worker_thread and self.worker_thread.is_alive():
            messagebox.showwarning("Aviso", "Já existe uma execução em andamento.")
            return

        try:
            steps = _parse_script_content(self.script_text.get("1.0", tk.END).strip())
            repetitions = int(self.repetitions_var.get())
            float(self.start_delay_var.get())
            float(self.delay_var.get())
        except (json.JSONDecodeError, ValueError, TypeError) as exc:
            messagebox.showerror("Erro", str(exc))
            return

        self.clear_console()
        self.stop_event.clear()
        self.execution_count += 1
        self.count_var.set(f"Count: {self.execution_count}")
        selected_table = self.selected_table_var.get().strip() or None
        execution_count = self.execution_count

        runner = ScriptRunner(
            self.log,
            self.stop_event.is_set,
            lambda: float(self.delay_var.get() or 0),
            lambda: float(self.start_delay_var.get() or 0),
        )

        def target() -> None:
            try:
                self.log(f"Execução iniciada. [count={execution_count}]", ConsoleTag.INFO.value)
                runner.run(steps, repetitions, selected_table, execution_count)
            except Exception as exc:
                self.log(f"ERRO: {exc}", ConsoleTag.ERROR.value)
            finally:
                self.log("Thread finalizada.", ConsoleTag.INFO.value)

        self.worker_thread = threading.Thread(target=target, daemon=True)
        self.worker_thread.start()

    def stop_execution(self) -> None:
        self.stop_event.set()
        self.execution_count = 0
        self.count_var.set("Count: 0")
        self.log("Solicitação de parada registrada.", ConsoleTag.WARNING.value)

    def clear_console(self) -> None:
        self.console_text.config(state="normal")
        self.console_text.delete("1.0", tk.END)
        self.console_text.config(state="disabled")

    def log(self, message: str, tag: ConsoleTag | str = ConsoleTag.DEFAULT.value) -> None:
        timestamp = time.strftime("%H:%M:%S")
        self.log_queue.put((f"[{timestamp}] {message}", tag))

    def process_log_queue(self) -> None:
        while not self.log_queue.empty():
            message, tag = self.log_queue.get()
            self.console_text.config(state="normal")
            self.console_text.insert(tk.END, message + "\n", tag)
            self.console_text.see(tk.END)
            self.console_text.config(state="disabled")
        self.after(Constants.LOG_POLL_INTERVAL_MS, self.process_log_queue)

    def update_mouse_position(self) -> None:
        try:
            x, y = pyautogui.position()
            self.mouse_position_var.set(f"Mouse: X={x} Y={y}")
            if x <= Constants.FAILSAFE_CORNER_THRESHOLD and y <= Constants.FAILSAFE_CORNER_THRESHOLD and self.worker_thread and self.worker_thread.is_alive():
                self.stop_execution()
        except Exception:
            self.mouse_position_var.set("Mouse: X=? Y=?")
        self.after(Constants.MOUSE_POLL_INTERVAL_MS, self.update_mouse_position)


if __name__ == "__main__":
    app = AutomationApp()
    app.mainloop()
