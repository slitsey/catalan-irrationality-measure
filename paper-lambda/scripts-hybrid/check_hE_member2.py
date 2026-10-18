# Independent check of Lemma E (Theorem hE) for both members e=0,1 and admissible m (not only r//8).
# Computes det Fu(X) in Q[X] exactly by Newton interpolation at the points x_k = k + 1/3 (different from the
# writer's 0..|C|), then v_p(den_F) = max(0, -min_k v_p(coef_k)), and compares with the bounds of Theorem hE:
#  (a) p=3 mod 4, 2p > r+2m, 5p+1 < 4r            :  v_p(den) <= 2r + 2e
#  (b) p=1 mod 4, p<r, 7p+1 > 4r+8m (>= if e=0)    :  v_p(den) <= 2(2r-p-K_p) + 3m + 4e
# and with the tropical value B_{m0}(p) of Prop. hdual (formula, not Hungarian).
import sys, os
if os.environ.get('PYLIBS'): sys.path.insert(0, os.environ['PYLIBS'])  # optional: dir with python-flint
from flint import fmpq, fmpq_mat, fmpq_poly

def vp(x, p):
    if x == 0: return 10**9
    n, d = int(x.p), int(x.q); v = 0
    while n % p == 0: n //= p; v += 1
    while d % p == 0: d //= p; v -= 1
    return v

def isprime(n):
    return n > 1 and all(n % d for d in range(2, int(n**0.5) + 1))

def run(r, m, e):
    b = r + 2*m
    top = b + 3
    F = [fmpq(0)]; Ps = [fmpq(0)]
    for k in range(1, top):
        F.append(F[-1] - fmpq(1, 4*k*(4*k-1)))
        Ps.append(Ps[-1] + fmpq(1, 16*k*k) - fmpq(1, (4*k-1)**2))
    def R(a, c):
        return Ps[a] if a == c else (F[a]-F[c]) / (4*(c-a))
    C = list(range(r)) + ([b] if e else [])
    Xp = [r+2*i for i in range(m)]; Yp = [r+2*i+1 for i in range(m)]
    rows = C + Xp; cols = C + Yp; n = len(rows); Cs = set(C)
    base = [[R(a, c) for c in cols] for a in rows]
    pts = [fmpq(3*k+1, 3) for k in range(len(C)+1)]
    vals = []
    for x in pts:
        M = fmpq_mat(n, n, [base[i][j] + (x if (rows[i] == cols[j] and rows[i] in Cs) else 0)
                            for i in range(n) for j in range(n)])
        vals.append(M.det())
    coef = list(vals)
    for j in range(1, len(pts)):
        for i in range(len(pts)-1, j-1, -1):
            coef[i] = (coef[i]-coef[i-1]) / (pts[i]-pts[i-j])
    poly = fmpq_poly([coef[-1]])
    for i in range(len(pts)-2, -1, -1):
        poly = poly*fmpq_poly([-pts[i], 1]) + coef[i]
    assert poly.degree() == len(C)
    cs = [poly[k] for k in range(poly.degree()+1)]
    m0 = r // 8
    out = []
    for p in range(11, 2*r):
        if not isprime(p) or p == 139: continue
        vden = max(0, -min(vp(c, p) for c in cs if c != 0))
        bound = None
        if p % 4 == 3 and 2*p > r+2*m and 5*p+1 < 4*r:
            bound = 2*r + 2*e; case = 'a'
        if p % 4 == 1 and p < r and (7*p+1 > 4*r+8*m or (e == 0 and 7*p+1 >= 4*r+8*m)):
            Kp = (3*p+1)//4; bound = 2*(2*r-p-Kp) + 3*m + 4*e; case = 'b'
        if bound is not None:
            out.append((p, case, vden, bound))
    return out

if __name__ == '__main__':
    fails = 0; tot = 0
    for spec in sys.argv[1:]:
        r, m, e = map(int, spec.split(','))
        res = run(r, m, e)
        for (p, case, vden, bound) in res:
            tot += 1; ok = vden <= bound; fails += (not ok)
            print(f'r={r} m={m} e={e} p={p} case={case} v_p(den)={vden} LemmaE_bound={bound} slack={bound-vden} {"OK" if ok else "FAIL"}', flush=True)
    print('total', tot, 'fails', fails)
# usage: python check_hE_member2.py 48,6,0 48,6,1 64,7,1 64,8,1 64,9,1 80,10,0 80,10,1 80,11,1   (r,m,e triples)
