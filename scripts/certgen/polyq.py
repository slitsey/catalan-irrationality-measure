"""Exact rational polynomial tools mirroring CatalanMeasure/Cert/ListPoly.lean.

Polynomials are lists of Fractions, constant term first.  The functions lp_* here compute
exactly what the Lean definitions compute, so a check that passes here passes in Lean."""
from fractions import Fraction as F


def lp_add(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def lp_smul(c, p):
    return [c * a for a in p]


def lp_mul(p, q):
    if not p or not q:
        return []
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                out[i + j] += a * b
    return out


def lp_eval(p, x):
    acc = 0
    for c in reversed(p):
        acc = c + x * acc
    return acc


def lp_comp_aff(a, h, p):
    """p(a + h X), by Horner (same as the Lean definition)."""
    out = []
    for c in reversed(p):
        out = lp_add([c], lp_mul([a, h], out))
    return out


def taylor_shift(p, a):
    """p(a + X) by synthetic division, O(d^2); equals lp_comp_aff(a, 1, p) as a polynomial."""
    c = list(p)
    n = len(c)
    for i in range(n - 1):
        for j in range(n - 2, i - 1, -1):
            c[j] += a * c[j + 1]
    return c


def comp_aff_fast(a, h, p):
    q = taylor_shift(p, a)
    hp = F(1)
    out = []
    for c in q:
        out.append(c * hp)
        hp *= h
    return out


def mobius(p, a, b):
    """(1+y)^d p(a + (b-a)/(1+y)) -- coefficients as in Lean's lpMobius."""
    B = comp_aff_fast(a, b - a, p)
    return taylor_shift(list(reversed(B)), F(1))


def sign_vars(T):
    s = [1 if c > 0 else -1 for c in T if c != 0]
    return sum(1 for i in range(len(s) - 1) if s[i] != s[i + 1])


def sign_check(T):
    nz = [c for c in T if c != 0]
    return bool(nz) and (all(c >= 0 for c in T) or all(c <= 0 for c in T))


def no_root_check(p, a, b):
    return a < b and sign_check(mobius(p, a, b))


def abs_sum(p):
    return sum(abs(c) for c in p)


def ratio_bound(A, Q, l, w):
    C = comp_aff_fast(l, w, Q)
    den = abs(C[0]) - abs_sum(C[1:])
    if den <= 0:
        return None
    return abs_sum(comp_aff_fast(l, w, A)) / den
