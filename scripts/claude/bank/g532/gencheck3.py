"""G8f generator part 3: rowInt (port of Charts/Rows.lean), regions, zones, and the Lean emission."""
import os, sys, re, json, math, itertools
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from gencheck import *
from gencheck2 import *

# ------------------------------------------------------------ rational moment tables (OAI.InternalCatalan)
from functools import lru_cache

@lru_cache(None)
def centralCoeff(l): return F(math.comb(2 * l, l), 4 ** l)
@lru_cache(None)
def momentScalar(i): return F(2) / ((i + 1) * centralCoeff(i // 2)) if i % 2 == 0 else F(0)
@lru_cache(None)
def boundaryMinus(d):
    if d == 0: return F(0)
    if d == 1: return F(2)
    d0 = d - 2
    return ((d0 + 1) * boundaryMinus(d0) + momentScalar(d0) + momentScalar(d0 + 1)) / (d0 + 2)
@lru_cache(None)
def boundaryPlus(d):
    if d <= 1: return F(0)
    d0 = d - 2
    return (d0 * boundaryPlus(d0) + F(2, d0 + 1)) / (d0 + 1)
@lru_cache(None)
def momentRat(i, j):
    if j <= i:
        return boundaryMinus(i - j) - sum((momentScalar(i - j + k) / (k + 1) for k in range(j)), F(0))
    return boundaryPlus(j - i) - sum((momentScalar(k) / (j - i + k + 1) for k in range(i)), F(0))
@lru_cache(None)
def momentRatSigned(i, j):
    if i >= 0: return momentRat(i, j)
    if i == -1: return boundaryPlus(j + 1)
    return F(0)
@lru_cache(None)
def harmonicRat(d, n): return sum((F(1, (k + 1) ** d) for k in range(n)), F(0))
@lru_cache(None)
def zetaRat(i, j):
    if i == j: return -harmonicRat(2, i)
    return (harmonicRat(1, i) - harmonicRat(1, j)) / (i - j)
def alphaQ(u, J): return momentRatSigned(u - 1, J)
def betaQ(u, J): return -F(3, 2) * zetaRat(u, J)

def Lmom(Ub, Jb):
    L = 1
    for u in range(Ub):
        for J in range(Jb):
            a = alphaQ(u, J).denominator; z = zetaRat(u, J).denominator
            l = a * z // math.gcd(a, z)
            L = L * l // math.gcd(L, l)
    return L
def Zmom(Ub, Jb): return 2 * Lmom(Ub, Jb)
def qscale(q, Z):
    assert Z % q.denominator == 0, (q, Z)
    return (Z // q.denominator) * q.numerator

# ------------------------------------------------------------ Chebyshev coefficient tables (Charts5/Prof146, Check/ProfK)
@lru_cache(None)
def uc(n):
    if n == 0: return (1,)
    if n == 1: return (0, 2)
    a = (0,) + uc(n - 1)
    b = uc(n - 2)
    m = max(len(a), len(b))
    return tuple(2 * (a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(m))
def ucz(n):
    if n >= 0: return list(uc(n))
    if n == -1: return []
    return [-x for x in uc(-n - 2)]
def padd(a, b):
    m = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(m)]
def psub(a, b):
    m = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(m)]
def shl(a): return [0] + list(a)
def mY(a): return psub(shl(a), a)
def mO(a): return padd(a, shl(a))
def vcz(n): return psub(ucz(n), ucz(n - 1))
def wcz(n): return padd(ucz(n), ucz(n - 1))
def tcz(n): return psub(ucz(n), shl(ucz(n - 1)))

def block_gt(k0, kk, u):
    kap = k0 + kk
    g = mO(vcz(kap)) if u < 2 else mY(wcz(kap))
    if u % 2 == 1: g = mY(g)
    t = wcz(kap) if u < 2 else vcz(kap)
    if u % 2 == 1: t = mY(t)
    return g, t
def cent_gt(k0, z):
    g = tcz(k0); t = ucz(k0 - 1)
    if z == 1: g = mY(g); t = mY(t)
    return g, t
class ProfK:
    def __init__(self, k0, b):
        self.k0, self.b = k0, b
        self.cache = {}
    def gt(self, k):
        if k in self.cache: return self.cache[k]
        b = self.b
        if k < 4 * b: r = block_gt(self.k0, k // 4, k % 4)
        elif k < 4 * b + 2: r = cent_gt(self.k0, k - 4 * b)
        else: r = ([], [])
        self.cache[k] = r; return r

def cf(f, i): return f[i] if 0 <= i < len(f) else 0
def rowInt(prof, Z, J, S, k):
    g, t = prof.gt(k)
    tot = 0
    for u in range(S + 3):
        tot += qscale(alphaQ(u, J), Z) * cf(g, S + 1 - u) + qscale(betaQ(u, J), Z) * cf(t, S - u)
    return tot

QB = 1922760350154212639070
SMOOTH = QB ** 40
def smooth(d): return d != 0 and SMOOTH % abs(d) == 0
