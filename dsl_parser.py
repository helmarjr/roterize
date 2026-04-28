from __future__ import annotations

import re
from typing import Any


# ── Default script shown when opening a new roteiro ──────────────────────────

DSL_DEFAULT_SCRIPT = """\
-- Variáveis: i (iteração), count (execuções), py (último resultado funcao_py)
-- [CAMPO] ou [tabela.CAMPO] = coluna da tabela CSV selecionada

secao("Bloco 1 — Mouse")

mouse(x=250, y=620, acao="clicar_esquerdo", info="Clicar no campo")

secao("Bloco 2 — Teclado")

teclado_digitar([NOME], info="Digitar nome da tabela")

teclado_pressionar("enter", info="Pressionar Enter")
"""

# ── Known function names ──────────────────────────────────────────────────────

FUNC_NAMES: frozenset[str] = frozenset({
    "esperar",
    "mouse",
    "printscreen",
    "secao",
    "teclado_atalho",
    "teclado_digitar",
    "teclado_funcao_py",
    "teclado_pressionar",
})


# ── Low-level text helpers ────────────────────────────────────────────────────

def find_comment_pos(line: str) -> int:
    """Return char index of the first '--' not inside a quoted string, or -1."""
    in_string = False
    i = 0
    while i < len(line):
        ch = line[i]
        if ch == '"':
            in_string = not in_string
        elif not in_string and line[i:i + 2] == "--":
            return i
        i += 1
    return -1


def _strip_comment(line: str) -> str:
    pos = find_comment_pos(line)
    return line[:pos].rstrip() if pos >= 0 else line


def _paren_depth_delta(s: str) -> int:
    """Net change in () depth, ignoring parens inside quoted strings."""
    depth = 0
    in_string = False
    for ch in s:
        if ch == '"':
            in_string = not in_string
        elif not in_string:
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
    return depth


# ── Argument tokeniser ────────────────────────────────────────────────────────

def _split_args(args_str: str) -> list[str]:
    """Split top-level comma-separated args respecting quoted strings and [brackets]."""
    parts: list[str] = []
    current: list[str] = []
    bracket_depth = 0
    in_string = False
    for ch in args_str:
        if ch == '"':
            in_string = not in_string
            current.append(ch)
        elif not in_string and ch == "[":
            bracket_depth += 1
            current.append(ch)
        elif not in_string and ch == "]":
            bracket_depth -= 1
            current.append(ch)
        elif not in_string and bracket_depth == 0 and ch == ",":
            token = "".join(current).strip()
            if token:
                parts.append(token)
            current = []
        else:
            current.append(ch)
    last = "".join(current).strip()
    if last:
        parts.append(last)
    return parts


def _parse_value(val: str) -> Any:
    """Convert a DSL value token to its Python representation."""
    val = val.strip()
    # Quoted string
    if len(val) >= 2 and val.startswith('"') and val.endswith('"'):
        return val[1:-1]
    # Booleans
    if val == "true":
        return True
    if val == "false":
        return False
    # Field reference  [CAMPO] or [tabela.CAMPO] → keep brackets for engine
    if val.startswith("[") and val.endswith("]"):
        return val
    # Integers
    try:
        return int(val)
    except ValueError:
        pass
    # Floats
    try:
        return float(val)
    except ValueError:
        pass
    # Expression / identifier (i, count, py, arithmetic)
    return val


def _parse_named_args(args_str: str) -> dict[str, Any]:
    """Parse 'key=value, ...' into a dict; positional args keyed as _pos0, _pos1 …"""
    result: dict[str, Any] = {}
    positional = 0
    for part in _split_args(args_str):
        m = re.match(r"^([a-zA-Z_][a-zA-Z0-9_]*)\s*=\s*(.+)$", part, re.DOTALL)
        if m:
            result[m.group(1)] = _parse_value(m.group(2).strip())
        else:
            result[f"_pos{positional}"] = _parse_value(part)
            positional += 1
    return result


# ── Step builders ─────────────────────────────────────────────────────────────

def _pop_common(args: dict[str, Any]) -> tuple[Any, Any]:
    return args.pop("info", None), args.pop("repetir", None)


def _apply_common(step: dict[str, Any], info: Any, repetir: Any) -> None:
    if info is not None and str(info) != "":
        step["info"] = str(info)
    if repetir is not None:
        step["repetir"] = repetir


def _digitar_value(valor: Any) -> str:
    """Map a DSL teclado_digitar value to the JSON digitar string."""
    # Bare variable references → {placeholder} syntax understood by the engine
    if valor in ("py", "i", "count"):
        return "{" + str(valor) + "}"
    return str(valor)


def _line_to_step(line: str) -> dict[str, Any] | None:
    line = line.strip()
    if not line:
        return None

    m = re.match(r"^(\w+)\s*\((.*)\)\s*$", line, re.DOTALL)
    if not m:
        raise SyntaxError(f"Sintaxe inválida: {line!r}")

    func = m.group(1)
    args = _parse_named_args(m.group(2))

    # ── secao ──────────────────────────────────────────────────────────────
    if func == "secao":
        texto = args.get("_pos0", args.get("texto", ""))
        return {"secao": str(texto)}

    # ── esperar ────────────────────────────────────────────────────────────
    if func == "esperar":
        secs = float(args.get("_pos0", args.get("segundos", 0)))
        return {"info": f"esperar {secs}s", "esperar": {"depois": secs}}

    # ── mouse ──────────────────────────────────────────────────────────────
    if func == "mouse":
        info, repetir = _pop_common(args)
        x = args.get("x")
        y = args.get("y")
        acao = args.get("acao")
        missing = [k for k, v in (("x", x), ("y", y), ("acao", acao)) if v is None]
        if missing:
            raise ValueError(f"mouse() requer: {', '.join(missing)}")
        step: dict[str, Any] = {"mouse": {"x": x, "y": y, "acao": acao}}
        _apply_common(step, info, repetir)
        return step

    # ── teclado_digitar ────────────────────────────────────────────────────
    if func == "teclado_digitar":
        info, repetir = _pop_common(args)
        variavel_py = bool(args.pop("variavel_py", False))
        valor = args.get("_pos0", args.get("valor"))
        if valor is None:
            raise ValueError("teclado_digitar() requer o valor (string, [CAMPO] ou variável)")
        if variavel_py:
            raw = str(valor)
            field_ref = raw[1:-1] if raw.startswith("[") and raw.endswith("]") else raw
            step = {"teclado": {"guardar_py": field_ref}}
        else:
            step = {"teclado": {"digitar": _digitar_value(valor)}}
        _apply_common(step, info, repetir)
        return step

    # ── teclado_atalho ─────────────────────────────────────────────────────
    if func == "teclado_atalho":
        info, repetir = _pop_common(args)
        teclas = args.get("_pos0", args.get("teclas"))
        if teclas is None:
            raise ValueError("teclado_atalho() requer as teclas")
        step = {"teclado": {"atalho": str(teclas)}}
        _apply_common(step, info, repetir)
        return step

    # ── teclado_pressionar ─────────────────────────────────────────────────
    if func == "teclado_pressionar":
        info, repetir = _pop_common(args)
        tecla = args.get("_pos0", args.get("tecla"))
        if tecla is None:
            raise ValueError("teclado_pressionar() requer a tecla")
        step = {"teclado": {"pressionar": str(tecla)}}
        _apply_common(step, info, repetir)
        return step

    # ── teclado_funcao_py ──────────────────────────────────────────────────
    if func == "teclado_funcao_py":
        info, repetir = _pop_common(args)
        colar = bool(args.pop("colar", True))
        funcao = args.get("_pos0", args.get("funcao"))
        if funcao is None:
            raise ValueError("teclado_funcao_py() requer o nome da função")
        step = {"teclado": {"funcao_py": str(funcao), "colar": colar}}
        _apply_common(step, info, repetir)
        return step

    # ── printscreen ────────────────────────────────────────────────────────
    if func == "printscreen":
        info, repetir = _pop_common(args)
        required = ("pasta", "nome_arquivo", "formato", "sobrescrever", "x", "y", "largura", "altura")
        vals = {k: args.get(k) for k in required}
        missing = [k for k, v in vals.items() if v is None]
        if missing:
            raise ValueError(f"printscreen() requer: {', '.join(missing)}")
        step = {
            "printscreen": {
                "pasta": str(vals["pasta"]),
                "nome_arquivo": str(vals["nome_arquivo"]),
                "formato": str(vals["formato"]),
                "sobrescrever": bool(vals["sobrescrever"]),
                "regiao": {
                    "x": vals["x"],
                    "y": vals["y"],
                    "largura": vals["largura"],
                    "altura": vals["altura"],
                },
            }
        }
        _apply_common(step, info, repetir)
        return step

    raise SyntaxError(
        f"Função desconhecida: {func!r}. "
        f"Disponíveis: {', '.join(sorted(FUNC_NAMES))}"
    )


# ── Public API ────────────────────────────────────────────────────────────────

def parse_dsl(text: str) -> list[dict[str, Any]]:
    """Parse a DSL roteiro text and return a list of JSON step dicts."""
    # Pass 1 — strip comments line-by-line and join logical lines split across
    # multiple physical lines (a call is complete when paren depth returns to 0).
    logical: list[str] = []
    current_parts: list[str] = []
    depth = 0

    for raw in text.splitlines():
        clean = _strip_comment(raw).rstrip()
        stripped = clean.strip()
        if not stripped and depth == 0:
            continue
        depth += _paren_depth_delta(stripped)
        if stripped:
            current_parts.append(stripped)
        if depth <= 0 and current_parts:
            logical.append(" ".join(current_parts))
            current_parts = []
            depth = 0

    if current_parts:
        logical.append(" ".join(current_parts))

    # Pass 2 — convert each logical line to a step dict
    steps: list[dict[str, Any]] = []
    for idx, line in enumerate(logical, 1):
        if not line.strip():
            continue
        try:
            step = _line_to_step(line)
            if step is not None:
                steps.append(step)
        except (SyntaxError, ValueError) as exc:
            raise ValueError(f"Linha {idx}: {exc}") from exc

    return steps


def is_dsl_content(text: str) -> bool:
    """Return True if *text* looks like DSL (not legacy JSON)."""
    stripped = text.strip()
    return bool(stripped) and not (stripped.startswith("[") or stripped.startswith("{"))


# ── JSON → DSL converter ──────────────────────────────────────────────────────

def _num(v: float | int) -> str:
    """Format a number removing unnecessary .0 suffix."""
    if isinstance(v, float) and v == int(v):
        return str(int(v))
    return str(v)


def _esc(s: Any) -> str:
    """Escape double quotes inside a DSL string value."""
    return str(s).replace("\\", "\\\\").replace('"', '\\"')


def _val(v: Any) -> str:
    """Format a value for DSL output (no quotes for numbers/expressions)."""
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, float):
        return _num(v)
    return str(v)


def _parse_wait_dict(wait: Any) -> tuple[float, float]:
    if not isinstance(wait, dict):
        return 0.0, 0.0
    return float(wait.get("antes", 0)), float(wait.get("depois", 0))


def _common(info: Any, repetir: Any) -> str:
    parts: list[str] = []
    if info:
        parts.append(f', info="{_esc(info)}"')
    if repetir is not None:
        parts.append(f", repetir={_val(repetir) if isinstance(repetir, (int, float)) else repetir}")
    return "".join(parts)


def _action_to_dsl(step: dict[str, Any], info: Any, repetir: Any) -> str | None:
    mouse      = step.get("mouse")
    teclado    = step.get("teclado")
    printscreen = step.get("printscreen")
    cx = _common(info, repetir)

    if isinstance(mouse, dict):
        x    = _val(mouse.get("x", 0))
        y    = _val(mouse.get("y", 0))
        acao = mouse.get("acao", "")
        return f'mouse(x={x}, y={y}, acao="{acao}"{cx})'

    if isinstance(teclado, dict):
        colar       = teclado.get("colar", True)
        action_keys = [k for k in teclado if k != "colar"]
        if not action_keys:
            return None
        act = action_keys[0]
        val = teclado[act]

        if act == "digitar":
            return f'teclado_digitar("{_esc(val)}"{cx})'
        if act == "campo_tabela":
            return f"teclado_digitar([{val}]{cx})"
        if act == "atalho":
            return f'teclado_atalho("{_esc(val)}"{cx})'
        if act == "pressionar":
            return f'teclado_pressionar("{_esc(val)}"{cx})'
        if act == "funcao_py":
            colar_s = "true" if colar else "false"
            return f'teclado_funcao_py("{_esc(val)}", colar={colar_s}{cx})'
        if act == "guardar_py":
            return f"teclado_digitar([{val}], variavel_py=true{cx})"
        return None

    if isinstance(printscreen, dict):
        pasta = _esc(printscreen.get("pasta", ""))
        nome  = _esc(printscreen.get("nome_arquivo", ""))
        fmt   = printscreen.get("formato", "png")
        sob   = "true" if printscreen.get("sobrescrever", False) else "false"
        reg   = printscreen.get("regiao") or {}
        x, y  = _val(reg.get("x", 0)),       _val(reg.get("y", 0))
        w, h  = _val(reg.get("largura", 1920)), _val(reg.get("altura", 1080))
        info_p = f', info="{_esc(info)}"' if info else ""
        rep_p  = f", repetir={_val(repetir) if isinstance(repetir, (int, float)) else repetir}" if repetir is not None else ""
        return (
            f'printscreen(pasta="{pasta}", nome_arquivo="{nome}",\n'
            f'            formato="{fmt}", sobrescrever={sob},\n'
            f'            x={x}, y={y}, largura={w}, altura={h}'
            f'{info_p}{rep_p})'
        )

    return None


def json_to_dsl(steps: list[dict[str, Any]]) -> str:
    """Convert a list of JSON step dicts to DSL text."""
    lines: list[str] = []

    for step in steps:
        # Section marker
        if "secao" in step and set(step.keys()) <= {"secao"}:
            lines.append(f'secao("{_esc(step["secao"])}")')
            lines.append("")
            continue

        info       = step.get("info") or step.get("obs")
        repetir    = step.get("repetir")
        bef, aft   = _parse_wait_dict(step.get("esperar"))

        if bef > 0:
            lines.append(f"esperar({_num(bef)})")

        dsl_line = _action_to_dsl(step, info, repetir)

        if dsl_line:
            lines.append(dsl_line)
        elif info:
            lines.append(f"-- {info}")

        if aft > 0:
            lines.append(f"esperar({_num(aft)})")

        if dsl_line or bef > 0 or aft > 0 or info:
            lines.append("")

    while lines and lines[-1] == "":
        lines.pop()

    return ("\n".join(lines) + "\n") if lines else "\n"
