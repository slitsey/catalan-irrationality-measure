# DV shared helpers (independent of DN/DQ code)
import sys
import os
if os.environ.get('PYLIBS'): sys.path.insert(0, os.environ['PYLIBS'])  # optional: directory with python-flint, gmpy2
from flint import fmpq, fmpq_mat
import gmpy2

def vq(x, p):
    if x == 0: return 10**9
    n, d = gmpy2.mpz(int(x.p)), gmpy2.mpz(int(x.q))
    return int(gmpy2.remove(n, p)[1]) - int(gmpy2.remove(d, p)[1])

def hungarian_max(W):
    n = len(W); INF = 10**18
    cost = [[-W[i][j] for j in range(n)] for i in range(n)]
    u = [0]*(n+1); v = [0]*(n+1); p = [0]*(n+1); way = [0]*(n+1)
    for i in range(1, n+1):
        p[0] = i; j0 = 0; minv = [INF]*(n+1); used = [False]*(n+1)
        while True:
            used[j0] = True; i0 = p[j0]; delta = INF; j1 = 0
            for j in range(1, n+1):
                if not used[j]:
                    cur = cost[i0-1][j-1] - u[i0] - v[j]
                    if cur < minv[j]: minv[j] = cur; way[j] = j0
                    if minv[j] < delta: delta = minv[j]; j1 = j
            for j in range(n+1):
                if used[j]: u[p[j]] += delta; v[j] -= delta
                else: minv[j] -= delta
            j0 = j1
            if p[j0] == 0: break
        while True:
            j1 = way[j0]; p[j0] = p[j1]; j0 = j1
            if j0 == 0: break
    return -sum(cost[p[j]-1][j-1] for j in range(1, n+1))

class Frame:
    def __init__(s, r):
        s.r = r; s.m = m = r // 8; s.top = top = r + 2*m + 1
        F = [fmpq(0)]; Ps = [fmpq(0)]
        for k in range(1, top):
            F.append(F[-1] - fmpq(1, 4*k*(4*k-1)))
            Ps.append(Ps[-1] + fmpq(1, 16*k*k) - fmpq(1, (4*k-1)**2))
        s.F, s.Ps = F, Ps
        s.C = list(range(r)); s.Xr = [r+2*i for i in range(m)]; s.Yc = [r+2*i+1 for i in range(m)]
        s.rows = s.C + s.Xr; s.cols = s.C + s.Yc
        s.primes = [p for p in range(int(0.6*r)+1, int(1.1*r)+1) if gmpy2.is_prime(p)]
    def R(s, a, b): return s.Ps[a] if a == b else (s.F[a]-s.F[b]) / (4*(b-a))
    def clean(s, p):
        return not any(s.r <= k < s.r+2*s.m for k in range(1, s.top) if k*(4*k-1) % p == 0)
    def taus(s, p):
        r = s.r
        def w(a, b):
            x = s.R(a, b)
            val = vq(x, p) if (a != b or a >= r) else min(vq(x, p), 0)
            return max(0, -val)
        WA = [[w(a, b) for b in s.C] for a in s.C]
        WF = [[w(a, b) for b in s.cols] for a in s.rows]
        return hungarian_max(WA), hungarian_max(WF)
