"""Root isolation and bracket planning for a derivative numerator A on a domain.

Produces a cover of the domain by breakpoints b_0 < ... < b_n with each piece tagged
'gap' (no root of A, certified by the Moebius sign check) or 'bracket' (short interval
containing a root)."""
from fractions import Fraction as F
import math
from polyq import mobius, sign_vars, sign_check, lp_eval


def isolate(A, a, b, maxdepth=60):
    """Vincent-Collins-Akritas bisection: list of (a, b, v) with v = 0 or 1 sign variations."""
    out, stack = [], [(a, b, 0)]
    while stack:
        lo, hi, d = stack.pop()
        T = mobius(A, lo, hi)
        v = sign_vars(T)
        if v == 0 and sign_check(T):
            out.append((lo, hi, 0))
        elif v == 1:
            out.append((lo, hi, 1))
        else:
            if d > maxdepth:
                raise RuntimeError(f'no isolation near {float(lo)}')
            mid = round_mid(lo, hi)
            if lp_eval(A, mid) == 0:
                raise RuntimeError('rational root')
            stack.append((mid, hi, d + 1))
            stack.append((lo, mid, d + 1))
    return sorted(out)


def round_mid(lo, hi):
    """A short decimal near the midpoint."""
    w = hi - lo
    digits = max(2, int(-math.floor(math.log10(float(w)))) + 2)
    m = (lo + hi) / 2
    return F(round(m * 10**digits), 10**digits)


def refine_root(A, lo, hi, width):
    """Bisect on the sign of A (one simple root inside) until hi - lo <= width."""
    slo = lp_eval(A, lo) > 0
    while hi - lo > width:
        mid = round_mid(lo, hi)
        if not (lo < mid < hi):
            mid = (lo + hi) / 2
        sm = lp_eval(A, mid)
        if sm == 0:
            return mid, mid
        if (sm > 0) == slo:
            lo = mid
        else:
            hi = mid
    return lo, hi


def plan(A, a, b, w=F(2, 10**7), excluded=()):
    """Breakpoint plan covering (a, b).  Returns list of (lo, hi, kind)."""
    pieces = []
    for lo, hi, v in isolate(A, a, b):
        if v == 0:
            pieces.append((lo, hi, 'gap'))
            continue
        r0, r1 = refine_root(A, lo, hi, w / 4)
        g = 10**7
        l = F(math.floor(r0 * g), g) - F(1, g)
        r = l + w
        while r < r1:
            r += F(1, g)
        l = max(l, lo); r = min(r, hi)
        for glo, ghi in ((lo, l), (r, hi)):
            if glo < ghi:
                for p in isolate(A, glo, ghi):
                    assert p[2] == 0, 'second root next to a bracket'
                    pieces.append((p[0], p[1], 'gap'))
        pieces.append((l, r, 'bracket'))
    pieces.sort()
    # breakpoints must not be roots of A (checked in Lean)
    for lo, hi, kind in pieces:
        for pt in (lo, hi):
            if pt not in excluded and lp_eval(A, pt) == 0:
                raise RuntimeError(f'breakpoint {pt} is a root')
    return pieces
