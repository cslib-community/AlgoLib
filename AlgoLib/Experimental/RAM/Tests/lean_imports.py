"""Read explicit Lean imports without requiring a Lean installation.

The supported header grammar follows Lean 4.30's Parser/Module/Syntax.lean:
``[module] [prelude] ([public] [meta] import [all] moduleName)*``.
Whitespace and ordinary nested comments may separate tokens. Each import takes
ONE module name; repeated import declarations may share a line. Doc comments
start the body, as they do in Lean. Imports inside the body are not dependencies.

Module names must use ordinary dotted ASCII identifiers (including primes, !,
and ?). Escaped/Unicode module names fail explicitly until support is added.
For an unambiguous boundary, put the first body command on a separate line from
the final import. Unsupported or malformed header forms raise ImportParseError
with a source location; they are never silently treated as additional imports.

Only explicit imports are returned, in source order. Implicit Init dependencies
and import visibility do not affect the repository's local dependency graph.
"""
from dataclasses import dataclass
from pathlib import Path
import re


class ImportParseError(ValueError):
    """A header cannot be inspected safely using the supported grammar."""


def _error(text: str, source: str, offset: int, message: str):
    line = text.count("\n", 0, offset) + 1
    column = offset - text.rfind("\n", 0, offset)
    raise ImportParseError(f"{source}:{line}:{column}: {message}")


def _comment_end(text: str, start: int, source: str) -> int:
    if text.startswith("--", start):
        end = text.find("\n", start)
        return len(text) if end < 0 else end
    depth, position = 1, start + 2
    while position < len(text):
        if text.startswith("/-", position):
            depth += 1
            position += 2
        elif text.startswith("-/", position):
            depth -= 1
            position += 2
            if depth == 0:
                return position
        else:
            position += 1
    _error(text, source, start, "unterminated block comment")


def _string_end(text: str, start: int, source: str) -> int:
    position = start + 1
    while position < len(text):
        if text[position] == "\\":
            position += 2
        elif text[position] == '"':
            return position + 1
        else:
            position += 1
    _error(text, source, start, "unterminated string literal")


def _escaped_identifier_end(text: str, start: int, source: str) -> int:
    end = text.find("»", start + 1)
    if end < 0:
        _error(text, source, start, "unterminated escaped identifier")
    return end + 1


def strip_comments(text: str, source: str = "<input>") -> str:
    """Replace comments with spaces, preserving offsets, newlines, and literals.

    Handles nested block comments, line comments, ordinary/raw strings, character
    literals, and escaped identifiers. This is lexical filtering, not name
    resolution: strings and syntax quotations remain present in the result.
    """
    result = list(text)

    def blank(start, end):
        for index in range(start, end):
            if text[index] not in "\r\n":
                result[index] = " "

    def code(position, *, interpolation=False):
        depth = 1
        while position < len(text):
            if text.startswith(("--", "/-"), position):
                end = _comment_end(text, position, source)
                blank(position, end)
                position = end
            elif text[position] == "«":
                position = _escaped_identifier_end(text, position, source)
            elif text[position] == '"':
                # The conventional s!/m!/f! forms contain actual Lean expressions.
                position = interpolated(position) if position and text[position - 1] == "!" else \
                    _string_end(text, position, source)
            elif text[position] == "r" and (not position or not (
                    text[position - 1].isalnum() or text[position - 1] in "_'!?")) and \
                    (raw := re.match(r'r(#+)?"', text[position:])):
                closing = '"' + (raw[1] or "")
                end = text.find(closing, position + len(raw[0]))
                if end < 0:
                    _error(text, source, position, "unterminated raw string literal")
                position = end + len(closing)
            elif text[position] == "'" and (character := re.match(
                    r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\])'", text[position:])):
                position += len(character[0])
            elif interpolation and text[position] == "{":
                depth += 1
                position += 1
            elif interpolation and text[position] == "}":
                depth -= 1
                position += 1
                if depth == 0:
                    return position
            else:
                position += 1
        if interpolation:
            _error(text, source, position, "unterminated string interpolation")
        return position

    def interpolated(start):
        position = start + 1
        while position < len(text):
            if text[position] == "\\":
                position += 2
            elif text[position] == '"':
                return position + 1
            elif text[position] == "{":
                position = code(position + 1, interpolation=True)
            else:
                position += 1
        _error(text, source, start, "unterminated interpolated string literal")

    code(0)
    return "".join(result)


@dataclass(frozen=True)
class _Token:
    value: str
    start: int
    end: int


class _Header:
    def __init__(self, text: str, source: str):
        self.text, self.source, self.position = text, source, 0
        self.tokens = []

    def fail(self, token: _Token, message: str):
        _error(self.text, self.source, token.start, message)

    def next_token(self) -> _Token:
        text = self.text
        while self.position < len(text):
            start = self.position
            if text[start].isspace():
                if text[start] == "\t":
                    _error(text, self.source, start, "tabs are not permitted in Lean headers; use spaces")
                self.position += 1
            elif text.startswith(("/--", "/-!"), start):
                self.position = _comment_end(text, start, self.source)
                return _Token("<doc-comment>", start, self.position)
            elif text.startswith(("--", "/-"), start):
                self.position = _comment_end(text, start, self.source)
            else:
                break
        start = self.position
        if start == len(text):
            return _Token("", start, start)
        if text[start] == '"':
            self.position = _string_end(text, start, self.source)
        elif text[start] == "«":
            self.position = _escaped_identifier_end(text, start, self.source)
        elif text[start].isalnum() or text[start] == "_":
            self.position += 1
            while self.position < len(text) and (text[self.position].isalnum() or
                    text[self.position] in "_.'!?"):
                self.position += 1
        else:
            self.position += 1
        return _Token(text[start:self.position], start, self.position)

    def peek(self, ahead=0) -> _Token:
        while len(self.tokens) <= ahead:
            self.tokens.append(self.next_token())
        return self.tokens[ahead]

    def take(self) -> _Token:
        token = self.peek()
        self.tokens.pop(0)
        return token


_MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*\Z")
_MODIFIERS = {"public", "meta", "private", "protected", "local", "scoped", "noncomputable", "unsafe", "all"}
_HEADER_WORDS = _MODIFIERS | {"import", "module", "prelude"}


def parse_imports(text: str, source: str = "<input>") -> list[str]:
    """Parse the supported header, rejecting uncertain import syntax explicitly."""
    header = _Header(text, source)
    is_module = header.peek().value == "module"
    if is_module:
        header.take()
    if header.peek().value == "prelude":
        header.take()
    imports = []
    previous = None
    while True:
        token = header.peek()
        modifiers = []
        while header.peek(len(modifiers)).value in _MODIFIERS:
            modifiers.append(header.peek(len(modifiers)).value)
        is_import = header.peek(len(modifiers)).value == "import"
        if not is_import:
            if token.value in {"module", "prelude"}:
                header.fail(token, "module/prelude must precede all imports and may occur only once")
            if previous is not None and token.value and "\n" not in text[previous.end:token.start]:
                header.fail(token, "unexpected text after import; use one module per import and put body commands on a new line")
            return imports
        if modifiers not in ([], ["public"], ["meta"], ["public", "meta"]):
            header.fail(token, "unsupported import modifiers; expected [public] [meta] import")
        for _ in modifiers:
            header.take()
        header.take()  # import
        import_all = header.peek().value == "all"
        if import_all:
            header.take()
        if (modifiers or import_all) and not is_module:
            header.fail(token, "public/meta/import all require a leading module declaration")
        if import_all and "public" in modifiers:
            header.fail(token, "public import all is invalid; use separate public import and import all declarations")
        name = header.take()
        if name.value in _HEADER_WORDS or not _MODULE.fullmatch(name.value):
            header.fail(name, "expected one ordinary dotted ASCII module name after import; escaped/Unicode names and partial names are unsupported")
        imports.append(name.value)
        previous = name


def read_imports(path: Path) -> list[str]:
    return parse_imports(path.read_text(), str(path))
