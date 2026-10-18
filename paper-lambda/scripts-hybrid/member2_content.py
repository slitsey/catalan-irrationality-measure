# EH: exact check of the content saving (v_p(den_F) <= tau_p - m) for the hybrid member 2 (C u {r+2m}), at clean band primes.
import sys, time
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from chk_lib import *
r = int(sys.argv[1]); fr = Frame(r); m = fr.m; b = r + 2*m
C2 = fr.C + [b]; rows = C2 + fr.Xr; cols = C2 + fr.Yc
fr.top = b + 2
# extend F, Ps tables
F = fr.F; Ps = fr.Ps
for k in range(len(F), fr.top + 1):
    F.append(F[-1] - fmpq(1, 4*k*(4*k-1))); Ps.append(Ps[-1] + fmpq(1, 16*k*k) - fmpq(1, (4*k-1)**2))
n = len(rows)
pts = list(range(len(C2) + 1)); vals = []
for x in pts:
    M = fmpq_mat(n, n, [fr.R(a, c) + (fmpq(x) if (a == c and a in C2) else 0) for a in rows for c in cols])
    vals.append(M.det())
from flint import fmpq_poly
coef = list(vals)
for j in range(1, len(pts)):
    for i in range(len(pts)-1, j-1, -1):
        coef[i] = (coef[i] - coef[i-1]) / (pts[i] - pts[i-j])
poly = fmpq_poly([coef[-1]])
for i in range(len(pts)-2, -1, -1):
    poly = poly * fmpq_poly([-pts[i], 1]) + coef[i]
cs = [poly[k] for k in range(poly.degree()+1)]
def taus(p):
    def w(a, c):
        x = fr.R(a, c)
        val = vq(x, p) if (a != c or a in C2) is False else (min(vq(x, p), 0) if a == c else vq(x, p))
        return max(0, -val)
    W = [[w(a, c) for c in cols] for a in rows]
    return hungarian_max(W)
print('r', r, 'm', m, 'b', b, 'deg', poly.degree())
for p in [q for q in range(int(0.6*r)+1, int(1.1*r)+1) if gmpy2.is_prime(q)]:
    vden = -min(vq(c, p) for c in cs if c != 0)
    t = taus(p)
    clean = not any(r <= k < r+2*m+1 for k in range(1, b+3) if (k*(4*k-1)) % p == 0)
    print(f'p={p} mod4={p%4} clean(zone+b)={clean} v_p(den)={vden} tau={t} deficit={t-vden} m={m}', flush=True)
