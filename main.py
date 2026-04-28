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


def _parse_script_json(content: str) -> list:
    parsed = json.loads(content)
    if not isinstance(parsed, list):
        raise ValueError("O roteiro deve ser uma lista JSON.")
    return parsed


DEFAULT_SCRIPT = """[
  {
    \"info\": \"Exemplo mouse\",
    \"mouse\": {\"x\": 250, \"y\": 620, \"acao\": \"clicar_esquerdo\"}
  },
  {
    \"info\": \"Exemplo com tabela selecionada\",
    \"teclado\": {\"campo_tabela\": \"NOME\"}
  },
  {
    \"info\": \"Exemplo pressionar ENTER\",
    \"teclado\": {\"pressionar\": \"enter\"}
  }
]"""


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
        else:
            raise ValueError(
                f"Subitem de teclado inválido: {action}. Use digitar, atalho, pressionar, campo_tabela ou funcao_py."
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
        super().__init__(master, title="CRUD de Roteiros (JSON)", geometry=Constants.SCRIPT_EDITOR_GEOMETRY)
        self._build_layout("Nome do arquivo (sem .json):")
        self.new_file()
        self.refresh_list()

    def _get_buttons(self) -> list[tuple[str, Callable]]:
        return [
            ("Novo", self.new_file),
            ("Salvar", self.save_file),
            ("Excluir", self.delete_file),
            ("Carregar na tela principal", self.load_into_main),
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
            _parse_script_json(content)
        except (json.JSONDecodeError, ValueError) as exc:
            messagebox.showerror("Erro de JSON", str(exc))
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
        self._sec_placeholders()
        self._sec_tabelas()
        self._sec_exemplos()

    # ── 1. Estrutura ──────────────────────────────────────────────────────────

    def _sec_estrutura(self) -> None:
        self._section("1.  ESTRUTURA GERAL", "sec_estrutura")
        self._nl()
        self._ins("  O roteiro é uma ", "body")
        self._ins("lista JSON", "field")
        self._ins(" onde cada elemento representa um passo da automação.\n", "body")
        self._ins("  Cada passo pode conter ", "body")
        self._ins("uma ação principal", "tip")
        self._ins(" (mouse, teclado ou printscreen) e campos auxiliares.\n", "body")
        self._code("""\
[
  { "secao": "Bloco 1 — Abrir janela" },

  { "info": "Clicar no campo",
    "mouse":   { "x": 400, "y": 300, "acao": "clicar_esquerdo" },
    "esperar": { "depois": 0.3 } },

  { "info": "Digitar valor da tabela",
    "teclado": { "campo_tabela": "NOME" } },

  { "secao": "Bloco 2 — Salvar" },

  { "info": "Salvar com atalho",
    "teclado": { "atalho": "ctrl+s" } }
]""")
        self._note("Somente 1 ação principal por passo. Nunca combine mouse + teclado no mesmo item.")

    # ── 2. Auxiliares ─────────────────────────────────────────────────────────

    def _sec_auxiliares(self) -> None:
        self._section("2.  CAMPOS AUXILIARES", "sec_aux")

        self._sub2("info")
        self._ins("  Descrição exibida no console durante a execução. Não afeta o comportamento.\n", "body")
        self._code('{ "info": "Abrindo janela de busca", "teclado": { "pressionar": "enter" } }')

        self._sub2("secao")
        self._ins("  Marcador de bloco lógico. Aparece em ", "body")
        self._ins("amarelo bold", "tip")
        self._ins(" no console. Não executa nenhuma ação.\n", "body")
        self._code('{ "secao": "PARTE 1 — ABRIR OBJETO" }')

        self._sub2("esperar")
        self._ins("  Pausa em segundos antes e/ou depois da ação.\n", "body")
        self._code("""\
{ "info": "...",
  "teclado": { "pressionar": "enter" },
  "esperar": { "antes": 0.5, "depois": 1.0 } }""")
        self._item("antes",  "pausa antes de executar")
        self._item("depois", "pausa após executar")

        self._sub2("repetir")
        self._ins("  Repete o passo N vezes. Aceita número ou expressão com variáveis.\n", "body")
        self._code("""\
{ "teclado": { "pressionar": "tab" }, "repetir": 3         }
{ "teclado": { "pressionar": "tab" }, "repetir": "i + 1"   }
{ "teclado": { "pressionar": "tab" }, "repetir": "count"   }
{ "teclado": { "pressionar": "tab" }, "repetir": "count*2" }""")
        self._item("i",     "índice da iteração atual (começa em 0)", "ph")
        self._item("count", "número de execuções acumuladas (começa em 1)", "ph")
        self._note("Operadores disponíveis:  + − * / // % **")

    # ── 3. Mouse ──────────────────────────────────────────────────────────────

    def _sec_mouse(self) -> None:
        self._section("3.  AÇÃO MOUSE", "sec_mouse")
        self._nl()
        self._ins('  Formato:  ', "muted")
        self._ins('"mouse": { "x": 800, "y": 500, "acao": "clicar_esquerdo" }', "inline")
        self._nl(2)
        self._ins("  Ações disponíveis:\n", "body")
        acoes = [
            ("clicar_esquerdo", "clique simples com botão esquerdo"),
            ("clicar_direito",  "clique simples com botão direito"),
            ("clicar_duplo",    "duplo clique com botão esquerdo"),
            ("mover",           "move o cursor sem clicar"),
            ("clicar_segurar",  "pressiona e segura o botão esquerdo"),
            ("clicar_soltar",   "solta o botão esquerdo"),
        ]
        for acao, desc in acoes:
            self._ins("    ")
            self._ins(f"{acao:<20}", "action")
            self._ins(f"→  {desc}\n", "muted")
        self._nl()
        self._ins("  Posicionamento dinâmico:\n", "body")
        self._ins("  Os campos ", "muted")
        self._ins("x", "field")
        self._ins(" e ", "muted")
        self._ins("y", "field")
        self._ins(" aceitam expressões com ", "muted")
        self._ins("{i}", "ph")
        self._ins(" e ", "muted")
        self._ins("{count}", "ph")
        self._ins(":\n", "muted")
        self._code("""\
{ "mouse": { "x": 3333, "y": "42 + (i * 20)", "acao": "clicar_esquerdo" } }
  ↑ i=0 → y=42  |  i=1 → y=62  |  i=2 → y=82""")
        self._note("Operadores disponíveis:  + − * / // % **")
        self._nl()
        self._note("Drag & drop: use clicar_segurar → mover → clicar_soltar em passos consecutivos.")
        self._code("""\
{ "mouse": { "x": 200, "y": 300, "acao": "clicar_segurar" }, "esperar": { "depois": 0.3 } },
{ "mouse": { "x": 600, "y": 300, "acao": "mover"          }, "esperar": { "depois": 0.1 } },
{ "mouse": { "x": 600, "y": 300, "acao": "clicar_soltar"  }, "esperar": { "depois": 1.0 } }""")

    # ── 4. Teclado ────────────────────────────────────────────────────────────

    def _sec_teclado(self) -> None:
        self._section("4.  AÇÃO TECLADO", "sec_teclado")
        self._nl()
        self._ins("  O objeto ", "body")
        self._ins('"teclado"', "field")
        self._ins(" deve conter exatamente ", "body")
        self._ins("uma chave", "tip")
        self._ins(" por passo.\n", "body")

        self._sub2("digitar")
        self._ins("  Cola um texto no campo com foco. Aceita placeholders.\n", "body")
        self._code("""\
{ "teclado": { "digitar": "texto fixo"        } }
{ "teclado": { "digitar": "Item_{i}"          } }
{ "teclado": { "digitar": "Execucao_{count}"  } }""")

        self._sub2("atalho")
        self._ins("  Executa uma combinação de teclas (hotkey).\n", "body")
        self._code("""\
{ "teclado": { "atalho": "ctrl+s"       } }
{ "teclado": { "atalho": "ctrl+shift+a" } }
{ "teclado": { "atalho": "alt+f4"       } }""")

        self._sub2("pressionar")
        self._ins("  Pressiona uma única tecla.\n", "body")
        self._code('{ "teclado": { "pressionar": "enter" } }')
        self._nl()
        self._ins("  Teclas comuns: ", "muted")
        teclas = "enter  tab  esc  space  backspace  delete  up  down  left  right  home  end  pageup  pagedown  F1…F12"
        self._ins(teclas + "\n", "inline")

        self._sub2("campo_tabela")
        self._ins("  Lê o próximo registro pendente de uma tabela CSV e cola o valor no campo com foco.\n", "body")
        self._code("""\
{ "teclado": { "campo_tabela": "NOME"          } }  ← tabela do dropdown
{ "teclado": { "campo_tabela": "clientes.EMAIL"} }  ← tabela específica""")
        self._bullet("Ao concluir a iteração com sucesso  →  STATUS = OK na linha usada")
        self._bullet("Se houver erro ou interrupção  →  rollback automático, linha volta para a fila")
        self._bullet("É possível usar mais de uma tabela no mesmo roteiro")

        self._sub2("funcao_py")
        self._ins("  Aplica uma função de ", "body")
        self._ins("transformacoes.py", "field")
        self._ins(" sobre o texto que está no clipboard.\n", "body")
        self._code('{ "teclado": { "atalho": "ctrl+c" }, "esperar": { "depois": 0.5 } }\n{ "teclado": { "funcao_py": "NOME_DA_FUNCAO" } }')
        self._note("Fluxo: Ctrl+C manual  →  lê clipboard  →  função(texto)  →  Ctrl+V com resultado.")
        self._nl()
        self._ins("  Use ", "body")
        self._ins('"colar": false', "field")
        self._ins(" para reter o resultado em ", "body")
        self._ins("{py}", "ph")
        self._ins(" sem colar automaticamente:\n", "body")
        self._code("""\
{ "teclado": { "atalho": "ctrl+c" }, "esperar": { "depois": 0.5 } }
{ "teclado": { "funcao_py": "extrair_tabela_do_from", "colar": false } }
{ "printscreen": { "pasta": "C:/prints", "nome_arquivo": "PRINT_{py}", "formato": "png" } }
{ "teclado": { "pressionar": "ctrl+v" } }  ← cole onde quiser depois""")
        self._note("{py} fica disponível como placeholder até o fim da iteração.")

    # ── 5. Printscreen ────────────────────────────────────────────────────────

    def _sec_printscreen(self) -> None:
        self._section("5.  AÇÃO PRINTSCREEN", "sec_print")
        self._code("""\
{ "info": "Capturar tela",
  "printscreen": {
    "pasta":        "C:/prints",
    "nome_arquivo": "Print_[clientes.NOME]_{count}",
    "formato":      "png",
    "sobrescrever": true,
    "regiao": { "x": 0, "y": 0, "largura": 1920, "altura": 1040 }
  }
}""")
        campos = [
            ("pasta",        "obrigatório",  "caminho da pasta de destino (criada automaticamente se não existir)"),
            ("nome_arquivo", "obrigatório",  "nome do arquivo sem extensão — aceita [ ] e placeholders"),
            ("formato",      "png*",         "png  |  jpg  |  jpeg  |  bmp"),
            ("sobrescrever", "false*",       "true = substitui arquivo existente"),
            ("regiao",       "opcional",     "captura apenas a área definida por x, y, largura, altura"),
        ]
        self._nl()
        for campo, default, desc in campos:
            self._ins("    ")
            self._ins(f"{campo:<16}", "field")
            self._ins(f"[{default}]  ", "value")
            self._ins(f"{desc}\n", "muted")

        self._sub2("Valores dinâmicos em nome_arquivo")
        exemplos = [
            ("[CAMPO]",         "coluna da tabela selecionada no dropdown"),
            ("[tabela.CAMPO]",  "coluna de uma tabela específica"),
            ("{count}",         "número de execuções acumuladas"),
            ("{i}",             "índice da iteração atual"),
        ]
        for token, desc in exemplos:
            self._ins("    ")
            self._ins(f"{token:<22}", "ph")
            self._ins(f"→  {desc}\n", "muted")
        self._code('"nome_arquivo": "Rel_[clientes.NOME]_exec{count}_iter{i}"')

    # ── 6. Placeholders ───────────────────────────────────────────────────────

    def _sec_placeholders(self) -> None:
        self._section("6.  PLACEHOLDERS", "sec_ph")
        self._nl()
        self._ins("  Disponíveis em: ", "muted")
        self._ins("digitar  campo_tabela  nome_arquivo  repetir\n", "inline")
        self._nl()
        rows = [
            ("{i}",     "índice da iteração atual dentro da execução  (começa em 0, reseta a cada Executar)"),
            ("{count}", "contador total de cliques em Executar na sessão  (começa em 1, acumula)"),
            ("{py}",    "último resultado de funcao_py com colar:false  (reseta a cada iteração)"),
        ]
        for ph, desc in rows:
            self._ins("    ")
            self._ins(f"{ph:<12}", "ph")
            self._ins(f"{desc}\n", "body")
        self._code("""\
{ "teclado": { "digitar":      "Arquivo_{count}_linha_{i}" } }
{ "teclado": { "campo_tabela": "NOME"                      } }
{ "printscreen": { "pasta": "C:/prints", "nome_arquivo": "Print_{count}_{i}", "formato": "png" } }
{ "teclado": { "pressionar": "tab" }, "repetir": "count + i" }
{ "teclado": { "funcao_py": "extrair_tabela_do_from", "colar": false } }
{ "printscreen": { "pasta": "C:/prints", "nome_arquivo": "PRINT_{py}_iter{i}", "formato": "png" } }""")

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
        self._item("(vazio)",   "registro pendente — será processado na próxima execução", "value")
        self._item("OK",        "registro já processado — ignorado nas próximas execuções", "action")
        self._note("Rollback automático: se a iteração falhar ou for interrompida, o STATUS não é gravado.")

    # ── 8. Exemplos ───────────────────────────────────────────────────────────

    def _sec_exemplos(self) -> None:
        self._section("8.  EXEMPLOS COMPLETOS", "sec_exemplos")

        self._sub("8.1  Fluxo básico com tabela")
        self._code("""\
[
  { "secao": "PREENCHER FORMULÁRIO" },

  { "info": "Clicar no campo nome",
    "mouse":   { "x": 400, "y": 300, "acao": "clicar_esquerdo" } },

  { "info": "Digitar nome da tabela",
    "teclado": { "campo_tabela": "NOME" } },

  { "info": "Avançar campo",
    "teclado": { "pressionar": "tab" } },

  { "info": "Salvar registro",
    "teclado": { "atalho": "ctrl+s" },
    "esperar": { "depois": 1.0 } }
]""")

        self._sub("8.2  Print com nome dinâmico e região")
        self._code("""\
[
  { "secao": "CAPTURAR TELA" },

  { "info": "Aguardar carregamento",
    "esperar": { "depois": 2.0 } },

  { "info": "Salvar print",
    "printscreen": {
      "pasta":        "C:/prints/exec_{count}",
      "nome_arquivo": "[tabela.CODIGO]_iter{i}",
      "formato":      "png",
      "sobrescrever": true,
      "regiao": { "x": 0, "y": 0, "largura": 1920, "altura": 1040 }
    }
  }
]""")

        self._sub("8.3  Drag and drop")
        self._code("""\
[
  { "secao": "ARRASTAR ELEMENTO" },

  { "info": "Segurar item",
    "mouse": { "x": 200, "y": 300, "acao": "clicar_segurar" },
    "esperar": { "depois": 0.3 } },

  { "info": "Mover para destino",
    "mouse": { "x": 600, "y": 300, "acao": "mover" },
    "esperar": { "depois": 0.1 } },

  { "info": "Soltar item",
    "mouse": { "x": 600, "y": 300, "acao": "clicar_soltar" },
    "esperar": { "depois": 1.5 } }
]""")

        self._sub("8.4  Múltiplas tabelas + count + secao")
        self._code("""\
[
  { "secao": "EXECUÇÃO {count} — CADASTRO DUPLO" },

  { "info": "Campo A — tabela_a",
    "teclado": { "campo_tabela": "tabela_a.NOME" } },

  { "info": "Campo B — tabela_b",
    "teclado": { "campo_tabela": "tabela_b.CODIGO" } },

  { "info": "Confirmar e aguardar",
    "teclado": { "pressionar": "enter" },
    "esperar": { "depois": 0.5 } }
]""")
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

    def _configure_script_tags(self) -> None:
        self.script_text.tag_configure("json_key", foreground="#93c5fd")
        self.script_text.tag_configure("json_string", foreground="#86efac")
        self.script_text.tag_configure("json_number", foreground="#fca5a5")
        self.script_text.tag_configure("json_boolean", foreground="#f9a8d4")
        self.script_text.tag_configure("json_brace", foreground="#cbd5e1")

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
        self.apply_json_highlight()
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

    def apply_json_highlight(self) -> None:
        content = self.script_text.get("1.0", "end-1c")
        for tag in ("json_key", "json_string", "json_number", "json_boolean", "json_brace"):
            self.script_text.tag_remove(tag, "1.0", tk.END)

        for match in re.finditer(r'"([^"\\]*(?:\\.[^"\\]*)*)"\s*:', content):
            start = f"1.0+{match.start()}c"
            end = f"1.0+{match.end() - 1}c"
            self.script_text.tag_add("json_key", start, end)

        for match in re.finditer(r':\s*"([^"\\]*(?:\\.[^"\\]*)*)"', content):
            colon_position = match.group(0).find('"')
            start = f"1.0+{match.start() + colon_position}c"
            end = f"1.0+{match.end()}c"
            self.script_text.tag_add("json_string", start, end)

        for match in re.finditer(r"\b-?\d+(?:\.\d+)?\b", content):
            start = f"1.0+{match.start()}c"
            end = f"1.0+{match.end()}c"
            self.script_text.tag_add("json_number", start, end)

        for match in re.finditer(r"\b(true|false|null)\b", content):
            start = f"1.0+{match.start()}c"
            end = f"1.0+{match.end()}c"
            self.script_text.tag_add("json_boolean", start, end)

        for match in re.finditer(r"[\{\}\[\]]", content):
            start = f"1.0+{match.start()}c"
            end = f"1.0+{match.end()}c"
            self.script_text.tag_add("json_brace", start, end)

    def _refresh_dropdown(self, combo: ttk.Combobox, var: tk.StringVar, directory: Path, pattern: str) -> None:
        values = [""] + [path.stem for path in sorted(directory.glob(pattern))]
        combo["values"] = values
        if var.get() not in values:
            var.set("")

    def refresh_script_dropdown(self) -> None:
        self._refresh_dropdown(self.script_combo, self.script_name_var, Paths.ROTEIROS_DIR, "*.json")

    def refresh_table_dropdown(self) -> None:
        self._refresh_dropdown(self.table_combo, self.selected_table_var, Paths.TABELAS_DIR, "*.csv")

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
            _parse_script_json(content)
        except (json.JSONDecodeError, ValueError) as exc:
            messagebox.showerror("Erro de JSON", str(exc))
            return

        path = Paths.ROTEIROS_DIR / f"{name}.json"
        path.write_text(content, encoding="utf-8")
        self.refresh_script_dropdown()
        self.script_name_var.set(name)
        self.log(f"Roteiro salvo: {path.name}", ConsoleTag.SUCCESS.value)
        messagebox.showinfo("OK", f"Roteiro salvo: {path.name}")

    def start_execution(self) -> None:
        if self.worker_thread and self.worker_thread.is_alive():
            messagebox.showwarning("Aviso", "Já existe uma execução em andamento.")
            return

        try:
            steps = _parse_script_json(self.script_text.get("1.0", tk.END).strip())
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
