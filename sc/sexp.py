"""S-expression reader/printer for SC-Lang.

Tokens: ints, #t/#f, symbols, ( ), ' quote sugar, ; comments.
"""
from __future__ import annotations


class ParseError(Exception):
    pass


def tokenize(src: str):
    toks = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c in " \t\r\n,":
            i += 1
        elif c == ";":
            while i < n and src[i] != "\n":
                i += 1
        elif c == "(" or c == "[":
            toks.append("(")
            i += 1
        elif c == ")" or c == "]":
            toks.append(")")
            i += 1
        elif c == "'":
            toks.append("'")
            i += 1
        elif c == '"':
            j = i + 1
            buf = []
            while j < n and src[j] != '"':
                if src[j] == "\\" and j + 1 < n:
                    buf.append(src[j + 1])
                    j += 2
                else:
                    buf.append(src[j])
                    j += 1
            if j >= n:
                raise ParseError("unterminated string")
            toks.append(("str", "".join(buf)))
            i = j + 1
        else:
            j = i
            while j < n and src[j] not in " \t\r\n()[]';\"":
                j += 1
            toks.append(src[i:j])
            i = j
    return toks


TRUE = ("bool", True)
FALSE = ("bool", False)


def _atom(tok):
    if isinstance(tok, tuple):
        return tok[1]  # string literal
    if tok == "#t":
        return True
    if tok == "#f":
        return False
    try:
        return int(tok, 10)
    except ValueError:
        return ("sym", tok)


def parse_all(src: str) -> list:
    toks = tokenize(src)
    pos = 0

    def parse():
        nonlocal pos
        if pos >= len(toks):
            raise ParseError("unexpected EOF")
        t = toks[pos]
        if t == "'":
            pos += 1
            return ["quote", parse()]
        if t == "(":
            pos += 1
            items = []
            while True:
                if pos >= len(toks):
                    raise ParseError("unclosed paren")
                if toks[pos] == ")":
                    pos += 1
                    return items
                items.append(parse())
        if t == ")":
            raise ParseError("unexpected )")
        pos += 1
        return _atom(t)

    forms = []
    while pos < len(toks):
        forms.append(parse())
    return forms


def pretty(x, depth=0):
    if isinstance(x, bool):
        return "#t" if x else "#f"
    if isinstance(x, int):
        return str(x)
    if isinstance(x, str):
        return '"%s"' % x
    if isinstance(x, tuple) and x and x[0] == "sym":
        return x[1]
    if isinstance(x, list):
        if depth > 40:
            return "(...)"
        return "(" + " ".join(pretty(e, depth + 1) for e in x) + ")"
    return str(x)
