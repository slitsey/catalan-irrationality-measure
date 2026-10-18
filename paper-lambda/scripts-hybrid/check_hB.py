# Check B(q) <= r f_j(q/r; a) + 1 (hand-proved with C0=0) for all odd q, several (r,m) with 8m<=r.
from fractions import Fraction as Fr
def g(j, th):
    if th <= Fr(4, 4+j): return 2
    if th <= 1: return 4 - Fr(4+j, 2)*th
    if th <= Fr(4, j): return 2 - Fr(j, 2)*th
    return 0
def eps(j, th, a):
    if th < 2*a: return 2*a - th*dist_fr(a/th)
    if th < Fr(4, 4+j): return a
    l = Fr(4+j, 4)*th - 1
    if th < Fr(4, 4+j)*(1+2*a): return min(a+2*l, 2*a+l)
    if th <= 1: return 4*a
    if th < 1+2*a: return 4*a - (th-1)
    if th < Fr(4, j): return 2*a
    if th < Fr(4, j)*(1+2*a): return 1+2*a - Fr(j, 4)*th
    return 0
def dist_fr(x):
    n = int(x); f = x - n
    return min(f, 1-f)
def B(q, r, m):
    j = 1 if q % 4 == 3 else 3; k = (j*q+1)//4; N = r+2*m
    n = min(r, k); dA = min(2*r, 2*(r-n) + 2*min(n, max(r-q, 0)))
    if q < 2*m: E = m + (m - q*dist_fr(Fr(m, q)))
    elif q <= r:
        U = max(k - r + q, 0); L = min(U, 2*m); E = min(2*m+L, m+L+U)
    elif q < N: E = 2*m + (N-q)
    elif k <= r: E = 2*m
    else: E = max(N-k, 0)
    return dA + E, j
worst = -10**9
for r in [97, 160, 241, 400, 1000, 4096, 10007]:
    for m in sorted({r//8, r//8 - 1, max(r//8 - 5, 1)}):
        a = Fr(m, r); w = -10**9
        for q in range(3, 4*(r+2*m)+8, 2):
            b, j = B(q, r, m); th = Fr(q, r)
            d = b - r*(g(j, th) + eps(j, th, a)); w = max(w, d)
        print(f'r={r} m={m} max_q [B - r f_j] = {float(w):.4f}'); worst = max(worst, w)
print('worst', float(worst), 'C0=0 holds:', worst <= 0)
