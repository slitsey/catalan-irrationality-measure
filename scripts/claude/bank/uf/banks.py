"""H13: generator settings of the UF window banks (thirds, fifths, sevenths a=1..6, lambda).

Everything that plan.py / gen.py / cover.py hard-wire for the thirds bank (q=3, o=2, c=3/10, band
3/10 < p/r <= 39/10, rho in {1,2}) is collected here as data; `plan_bank.py BANK` runs the same polygon
sampling for any bank WITHOUT generating Lean data (counts of polygons and families only).

Alternating geometry `altGeom c`: border size m(r) = min(ceil(c r/2), ceil((c r - 1)/2)) = ceil((c r - 1)/2)
(r even), N0 = r + 2 m, c = 2*alpha.  Two-term frame (q, o = q - a): singular indices of the window
[r, r+p) are the single multiple M1 = jm*p and the single pole P1 = (j1*p + o)/q with j1 = j0(rho) mod q,
j0 = -o * rho^{-1} (mod q), rho = p mod q; the runs R0, R1, R2 are the three pieces of [r, r+p) cut at them.
`left`/`right` = the banked band of H8 (theta = p/r in (left, right]); `P0` the smallest prime the UF
layer is used for (everything below goes to the pre/exc layers).  `nrm` = Fr.norm (the evaluation
points u0 change with it: M_Lean(u0) = nrm^-1 M_Py(nrm u0)).  Classes are the unit classes of p mod M.
"""
import sys, os
from fractions import Fraction as F
from math import gcd
sys.dont_write_bytecode = True


def bank(name, q, a, alpha, left, right, M, nrm=1, P0=None, sc=None):
    o = q - a
    c = 2 * alpha
    cls = [u for u in range(1, M) if gcd(u, M) == 1]
    rhos = sorted({u % q for u in cls})
    return dict(name=name, q=q, a=a, o=o, alpha=alpha, c=c, left=left, right=right, M=M, nrm=nrm,
                P0=P0 if P0 is not None else 20 * q, classes=cls, rhos=rhos, sc=sc)


BANKS = {
    'thirds': bank('thirds', 3, 1, F(3, 20), F(3, 10), F(39, 10), 6, 1, 60,
                   'hybrid-alpha-2026-10-27/sc/s-q3-a1-alpha3_20-lo3_10.json'),
    'fifths': bank('fifths', 5, 1, F(1, 9), F(2, 9), F(55, 9), 10, 1, None,
                   'scope-screen-2026-10-27/s-q5-a1-alpha1_9-lo2_9.json'),
    'lambda': bank('lambda', 4, 1, F(1, 10), F(1, 5), F(24, 5), 8, 16, None,
                   'hybrid-alpha-2026-10-27/sc/s-q4-a1-alpha1_10-lo1_5.json'),
}
for _a in range(1, 7):
    BANKS['sev%d' % _a] = bank('sev%d' % _a, 7, _a, F(1, 12), F(1, 6), F(49, 6), 14, 1, None,
                               'q4-mechanisms-uniform-2026-10-27/sc/s-q7-a1-alpha1_12-lo1_6.json' if _a == 1 else None)
BANKS['sevenths'] = BANKS['sev1']


def msize(B, r):
    """border size at even r (altGeom_borderSize): ceil((c r - 1)/2)."""
    num = B['c'] * r - 1
    n = -((-num.numerator) // (2 * num.denominator))
    return max(n, 0)


def pole_residue(B, rho):
    """j mod q with j*rho + o = 0 (mod q)."""
    q, o = B['q'], B['o']
    for j in range(q):
        if (j * rho + o) % q == 0: return j
    raise ValueError('p not prime to q')


def run_structure(B, r, p):
    """singular indices and runs of the window [r, r+p) (generalises plan.run_structure)."""
    q, o = B['q'], B['o']
    rho = p % q
    jm = (r - 1) // p + 1
    M1 = jm * p
    j1 = (q * r - o + p - 1) // p
    j0 = pole_residue(B, rho)
    while j1 % q != j0: j1 += 1
    assert (j1 * p + o) % q == 0
    P1 = (j1 * p + o) // q
    assert r <= P1 < r + p and r <= M1 < r + p, (r, p, M1, P1)
    sings = sorted([(M1, 'M', jm), (P1, 'P', j1)])
    m = msize(B, r)
    N0 = r + 2 * m
    runs = []
    s1, k1, jj1 = sings[0]; s2, k2, jj2 = sings[1]

    def st(s, k, j):
        if k == 'P': return s, (j // q, j)
        return s + 1, (j, q * j)
    runs.append(dict(idx=0, start=r, end=s1 - 1, stype=(r // p, (q * r - o) // p), lab='r'))
    a, ty = st(s1, k1, jj1)
    runs.append(dict(idx=1, start=a, end=s2 - 1, stype=ty, lab=(k1, jj1)))
    a, ty = st(s2, k2, jj2)
    runs.append(dict(idx=2, start=a, end=r + p - 1, stype=ty, lab=(k2, jj2)))
    return dict(rho=rho, jm=jm, j1=j1, order=''.join(s[1] for s in sings), runs=runs, N0=N0, m=m, s=(s1, s2),
                kinds=(k1, k2), js=(jj1, jj2))


def band(B, r):
    """integer p-range of the banked band at scale r (theta = p/r in (left, right])."""
    lo = int(B['left'] * r) + 1
    hi = int(B['right'] * r)
    return max(lo, B['P0']), hi
