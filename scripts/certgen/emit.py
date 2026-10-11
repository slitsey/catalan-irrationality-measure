"""Emit Lean source for certificate data."""
from fractions import Fraction as F


def q(x):
    x = F(x)
    if x.denominator == 1:
        return f"({x.numerator} : ℚ)"
    return f"({x.numerator} / {x.denominator} : ℚ)"


def qlist(xs, per_line=4):
    items = [q(x) for x in xs]
    lines = [", ".join(items[i:i + per_line]) for i in range(0, len(items), per_line)]
    return "[" + ",\n  ".join(lines) + "]"


def intlist(xs, per_line=8):
    items = [str(int(x)) for x in xs]
    lines = [", ".join(items[i:i + per_line]) for i in range(0, len(items), per_line)]
    return "[" + ",\n  ".join(lines) + "]"


def tails(ts):
    items = [f"⟨{q(a)}, {q(b)}, {q(c)}, {q(d)}⟩" for a, b, c, d in ts]
    return "[" + ",\n  ".join(items) + "]"
