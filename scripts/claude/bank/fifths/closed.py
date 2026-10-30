"""Python mirror of UFSimple.Closed closedPrice (for piece analysis)."""
from math import ceil
def ovl(r, R, a, b): return max(0, min(R, b + 1) - max(r, a))
def sub(a, b): return max(0, a - b)
def beta3(m, r, p, w0, w1):
    return ovl(r, r + 2*m, w0, w1) + ovl(r, r + 2*m, w0 + p, w1 + p) + ovl(r, r + 2*m, sub(w0, p), sub(w1, p))
def closedBound(m, r, p, t0, tv, w0):
    A = sub(min(tv + 1, r + 2*m), t0)
    return sub(2*(r + m), (m + sub(A, m) + sub(sub(A, m), sub(p, (sub(tv + 1, w0) + sub(2*m, beta3(m, r, p, w0, tv)))))))
def candB(r, p, k): return p*(r//p) + (p if k else 0)
def candL(rho, z): return rho if z else 0
def candU(p, rho, z): return p - 1 if z else sub(rho, 1)
def candUb(r, p, rho, k, z): return min(candU(p, rho, z), sub(r % p, 1)) if k else candU(p, rho, z)
def candOK(m, r, p, rho, k, z):
    B = candB(r, p, k); L = candL(rho, z)
    return max(r, B + L) < r + 2*m and max(r, B + L) <= B + candUb(r, p, rho, k, z) and ((not k) or 1 <= r % p)
def candPrice(m, r, p, rho, k, z):
    if candOK(m, r, p, rho, k, z):
        B = candB(r, p, k); L = candL(rho, z)
        return closedBound(m, r, p, max(r, B + L), B + candUb(r, p, rho, k, z), B + L)
    return 2*(r + m)
def closedPrice(m, r, p, rho):
    return min(candPrice(m, r, p, rho, k, z) for k in (False, True) for z in (False, True))
def border(r): return ceil((2*r/9 - 1)/2) if 2*r/9 - 1 > 0 else 0
