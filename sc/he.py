"""Homeomorphic embedding on configuration trees.

A configuration is rendered as a tree:
  ('#cfg', term_tree, ('#slots', v1, v2, ...))
where term_tree references variables by ('V', k) slot indices (coupling) and
each slot holds the value tree of the variable's symbolic value.

Embedding a ◁ b ("a embeds into b") means a is "no more specific" than b.
The whistle blows when an ANCESTOR configuration embeds into the CURRENT one,
i.e. we recognized the ancestor's shape inside the deeper current state —
the classic loop-growth signal.

Numbers use the HE3 divisibility guard: i ◁ j iff i == j or (sign match and
|j| >= 2·max(|i|,1)), which blocks immediate-successor loops while still
catching geometric growth.
"""
from __future__ import annotations


def diveq(i, j):
    if i == j:
        return True
    if isinstance(i, bool) or isinstance(j, bool):
        return False
    ai, aj = abs(i), abs(j)
    if ai == 0:
        return aj >= 2
    if (i > 0) != (j > 0):
        return False
    return aj >= 2 * ai


def embed(a, b, depth=0):
    """True iff tree a embeds into tree b."""
    if depth > 400:
        return True  # truncation biases toward the whistle (termination-safe)
    if not isinstance(a, tuple) or not a or not isinstance(b, tuple) or not b:
        try:
            return bool(a == b)
        except Exception:
            return a is b
    ta = a[0]
    tb = b[0]
    if ta == "#deep" or tb == "#deep":
        return True
    if ta == "D":
        # dynamic wildcard embeds only into dynamic wildcard
        return tb == "D"
    if tb == "D":
        return False
    if ta == "V":
        # coupling: variable slots must line up exactly
        return tb == "V" and a[1] == b[1]
    if ta == "i":
        return tb == "i" and diveq(a[1], b[1])
    if ta in ("b", "nil", "s", "e"):
        return a == b
    if ta == "#cons":
        if tb != "#cons":
            return False
        coupled = (embed(a[1], b[1], depth + 1) and embed(a[2], b[2], depth + 1))
        return coupled or embed(a, b[2], depth + 1)
    if ta == "#clo":
        if tb != "#clo" or a[1] != b[1] or len(a[2]) != len(b[2]):
            return False
        return all(embed(x, y, depth + 1) for x, y in zip(a[2], b[2]))
    if ta == "#case":
        if tb != "#case":
            return False
        return all(embed(x, y, depth + 1) for x, y in zip(a[1:], b[1:]))
    if ta == tb:
        # generic constructor: componentwise embedding; operator/name
        # positions (child 1 of #p/#mk) must match exactly
        if len(a) != len(b):
            return False
        if ta in ("#p", "#mk") and a[1] != b[1]:
            return False
        return all(embed(x, y, depth + 1) for x, y in zip(a[1:], b[1:]))
    # mixed kinds: no embedding
    return False
