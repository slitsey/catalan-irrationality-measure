# EH: exact check of Theorem hE (Lemma E) for admissible (r,m,e): v_p(den_F) <= bound, formal X (Gauss valuation), all primes meeting the hypotheses.
import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from chk_lib import *
from flint import fmpq_poly
def run(r, m, e):
    b = r + 2*m
    top = b + 3
    F = [fmpq(0)]; Ps = [fmpq(0)]
    for k in range(1, top+1):
        F.append(F[-1] - fmpq(1, 4*k*(4*k-1))); Ps.append(Ps[-1] + fmpq(1, 16*k*k) - fmpq(1, (4*k-1)**2))
    def R(a, c): return Ps[a] if a == c else (F[a]-F[c]) / (4*(c-a))
    C = list(range(r)) + ([b] if e else [])
    Xr = [r+2*i for i in range(m)]; Yc = [r+2*i+1 for i in range(m)]
    rows = C + Xr; cols = C + Yc; n = len(rows)
    pts = list(range(len(C)+1)); vals = []
    for x in pts:
        M = fmpq_mat(n, n, [R(a, c) + (fmpq(x) if (a == c and a in C) else 0) for a in rows for c in cols])
        vals.append(M.det())
    coef = list(vals)
    for j in range(1, len(pts)):
        for i in range(len(pts)-1, j-1, -1):
            coef[i] = (coef[i] - coef[i-1]) / (pts[i] - pts[i-j])
    poly = fmpq_poly([coef[-1]])
    for i in range(len(pts)-2, -1, -1):
        poly = poly * fmpq_poly([-pts[i], 1]) + coef[i]
    cs = [poly[k] for k in range(poly.degree()+1)]
    bad = 0; tested = 0
    for p in range(11, 2*r):
        if not gmpy2.is_prime(p) or p == 139: continue
        a3 = p % 4 == 3 and 2*p > r+2*m and 5*p+1 < 4*r
        Kp = (3*p+1)//4
        a1 = p % 4 == 1 and p < r and ((7*p+1 >= 4*r+8*m) if e == 0 else (7*p+1 > 4*r+8*m))
        if not (a3 or a1): continue
        v = min(vq(c, p) for c in cs if c != 0)   # Gauss valuation
        bound = -(2*r + 2*e) if a3 else -(2*(2*r-p-Kp) + 3*m + 4*e)
        tested += 1
        ok = v >= bound
        bad += (not ok)
        print(f'  r={r} m={m} e={e} p={p} class={"3" if a3 else "1"} v={v} bound={bound} {"OK" if ok else "FAIL"}', flush=True)
    return tested, bad
tot = 0; badt = 0
for (r, m, e) in [(40,5,0),(40,5,1),(40,6,0),(40,6,1),(48,6,0),(48,6,1),(48,7,1),(56,7,0),(56,7,1),(60,8,1)]:
    t, b = run(r, m, e); tot += t; badt += b
print('TOTAL tested', tot, 'FAIL', badt)
