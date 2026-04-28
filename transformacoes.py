from __future__ import annotations
import re


# Module-level prefix constants used in trocar_prefixo_tabela_rf
_PREFIX_ZS4_VCI = "ZS4_VCI_"
_PREFIX_VC_INTEGRATION = "VC_INTEGRATION_"
_PREFIX_S4H_TB = "S4H_TB_"


def manter(texto: str) -> str:
    """Returns the text unchanged."""
    return texto


def upper(texto: str) -> str:
    """Converts text to uppercase."""
    return texto.upper()


def lower(texto: str) -> str:
    """Converts text to lowercase."""
    return texto.lower()


def strip(texto: str) -> str:
    """Removes leading and trailing whitespace."""
    return texto.strip()


def somente_digitos(texto: str) -> str:
    """Keeps only digit characters from text."""
    return ''.join(ch for ch in texto if ch.isdigit())


def remover_espacos(texto: str) -> str:
    """Collapses multiple spaces into a single space."""
    return ' '.join(texto.split())


def capitalizar(texto: str) -> str:
    """Capitalizes the first letter of each word."""
    return texto.title()


def mandt(texto: str) -> str:
    """Returns the hardcoded MANDT value '500'."""
    return "'500'"


def extrair_tabela_do_from(texto: str) -> str:
    """Extracts the table name from a FROM clause in a SQL/CDS expression."""
    match = re.search(r'\bFROM\s+([^\s,;()]+)', texto, re.IGNORECASE)
    if match:
        return match.group(1).upper()
    return texto


def alias_uppercase(texto: str) -> str:
    """
    Remove alias existente e cria novo alias com o nome do campo em UPPERCASE.

    Se o texto contiver 'define view', processa todo o bloco CDS:
      - Localiza o corpo entre { } após 'define view'
      - Reescreve cada linha de campo com alias em UPPERCASE
      - Preserva anotações, linhas vazias e estrutura original

    Se for linha individual de campo:
      'vr_g_ng as Vrgng'   -> 'vr_g_ng as VR_G_NG'
      'bttype'             -> 'bttype as BTTYPE'
      'key rldnr as Rldnr' -> 'key rldnr as RLDNR'
    """

    def _processar_campo(linha: str) -> str:
        stripped = linha.strip()
        if not stripped or stripped in ('{', '}') or stripped.startswith('//') or stripped.startswith('@'):
            return linha
        virgula = ',' if stripped.endswith(',') else ''
        sem_virgula = stripped.rstrip(',').strip()
        m = re.match(r'^(key\s+)?(\w+)(\s+as\s+\w+)?$', sem_virgula, re.IGNORECASE)
        if m:
            indent = linha[:len(linha) - len(linha.lstrip())]
            prefixo = m.group(1) or ''
            campo = m.group(2)
            return f"{indent}{prefixo}{campo} as {campo.upper()}{virgula}"
        return linha

    # Modo bloco CDS completo
    if re.search(r'\bdefine\s+view\b', texto, re.IGNORECASE):
        linhas = texto.splitlines()
        resultado = []
        estado = 'antes'   # antes | aguarda_chave | dentro | depois
        for linha in linhas:
            if estado == 'antes':
                resultado.append(linha)
                if re.search(r'\bdefine\s+view\b', linha, re.IGNORECASE):
                    estado = 'aguarda_chave'
            elif estado == 'aguarda_chave':
                resultado.append(linha)
                if '{' in linha:
                    estado = 'dentro'
            elif estado == 'dentro':
                if '}' in linha.strip():
                    resultado.append(linha)
                    estado = 'depois'
                else:
                    resultado.append(_processar_campo(linha))
            else:
                resultado.append(linha)
        return '\n'.join(resultado)

    # Modo linha individual
    texto = texto.strip()
    match = re.match(r'^(key\s+)?(\w+)(\s+as\s+\w+)?', texto, re.IGNORECASE)
    if match:
        prefixo = match.group(1) or ''
        campo = match.group(2)
        return f"{prefixo}{campo} as {campo.upper()}"
    return texto


def trocar_prefixo_tabela_rf(texto: str) -> str:
    """
    Replaces known table name prefixes with the canonical S4H_TB_ prefix.

    Example:
        ZS4_VCI_A003        -> S4H_TB_A003
        VC_INTEGRATION_A003 -> S4H_TB_A003
    """
    texto = texto.strip()
    match = re.match(r'\w+', texto)
    texto = match.group(0) if match else texto

    if texto.startswith(_PREFIX_ZS4_VCI):
        return _PREFIX_S4H_TB + texto[len(_PREFIX_ZS4_VCI):]
    if texto.startswith(_PREFIX_VC_INTEGRATION):
        return _PREFIX_S4H_TB + texto[len(_PREFIX_VC_INTEGRATION):]
    return texto


TRANSFORMACOES = {
    'manter': manter,
    'upper': upper,
    'lower': lower,
    'strip': strip,
    'somente_digitos': somente_digitos,
    'remover_espacos': remover_espacos,
    'capitalizar': capitalizar,
    'alias_uppercase': alias_uppercase,
    'trocar_prefixo_tabela_rf': trocar_prefixo_tabela_rf,
    'mandt': mandt,
    'extrair_tabela_do_from': extrair_tabela_do_from,
}
