"""Run a callable in a thread with a large stack + high recursion limit.

The reference interpreter recurses in Python; deep-but-finite programs
(e.g. non-tail recursion of depth ~100k) need a big stack.
"""
from __future__ import annotations

import threading
import sys


def run_with_big_stack(fn, *args, stack_mb=512, limit=20_000_000, **kwargs):
    result = {}

    def target():
        old = sys.getrecursionlimit()
        sys.setrecursionlimit(limit)
        try:
            result["value"] = fn(*args, **kwargs)
        except BaseException as e:  # noqa
            result["error"] = e
        finally:
            sys.setrecursionlimit(old)

    size = stack_mb * 1024 * 1024
    while size >= 16 * 1024 * 1024:
        try:
            threading.stack_size(size)
            break
        except (ValueError, OverflowError, RuntimeError):
            size //= 2
    t = threading.Thread(target=target)
    t.start()
    t.join()
    if "error" in result:
        raise result["error"]
    return result["value"]


def run_program_bigstack(prog, fuel=200_000_000):
    from . import refinterp

    return run_with_big_stack(refinterp.run_program, prog, fuel)
