"""Trial data for the kappa = 2 dual, the derivative numerators/denominators of the two
fields, and float evaluation of the fields.

Trial sequence (OpenAI's barrierTrial):  u_k = cs[k-1]/1e8 + Re sum_j r_j z_j^k  (k >= 1).
Row field     X(x) = W2(x) - 4 T(p, x) - S(v, x),   x in [-1, 1), x != 0
Column field  Y(s) = Ws(s) + 2 T(v, s),             s in (0, 1)
with T(u, x) = sum_k u_k T_k(x)/k and S(u, x) = sum_k u_k x^k / k.
"""
import json
from fractions import Fraction as F
import numpy as np
from polyq import lp_add, lp_mul, lp_smul

E8 = 10**8


class Trial:
    def __init__(self, cs, tail):
        self.cs = [int(c) for c in cs]                 # integers, coefficient * 1e8
        self.tail = [(F(zr), F(zi), F(rr), F(ri)) for zr, zi, rr, ri in tail]

    def coeff(self, k):
        v = self.cs[k - 1] / E8 if k <= len(self.cs) else 0.0
        for zr, zi, rr, ri in self.tail:
            v += (complex(rr, ri) * complex(zr, zi) ** k).real
        return v

    def to_json(self):
        return dict(cs=self.cs, tail=[[str(a) for a in t] for t in self.tail])

    @staticmethod
    def from_json(d):
        return Trial(d['cs'], [tuple(F(a) for a in t) for t in d['tail']])


def from_basis(elems, coefs, K):
    """Optimizer basis (mono/geo/geoRe/geoIm) -> Trial, coefficients rounded to 1e-8."""
    cs = [0.0] * K
    tails = {}
    for (kind, a), c in zip(elems, coefs):
        if kind == 'mono':
            cs[int(a) - 1] += c
            continue
        z = complex(a)
        key = (round(z.real, 6), round(z.imag, 6))
        # merge a conjugate base into its upper-half-plane partner
        if key[1] < 0:
            key = (key[0], -key[1])
            conj = True
        else:
            conj = False
        if kind == 'geo' or kind == 'geoRe':
            r = complex(c, 0)
        elif kind == 'geoIm':
            r = complex(0, -c)
        if conj:
            r = r.conjugate()
        # a base z with Im z > 0 represents Re(r z^k); a pair (z, conj z) with weights r/2, conj r/2
        tails[key] = tails.get(key, 0) + r
    tail = []
    for (zr, zi), r in sorted(tails.items()):
        tail.append((F(str(zr)), F(str(zi)), F(round(r.real * E8), E8), F(round(r.imag * E8), E8)))
    return Trial([round(c * E8) for c in cs], tail)


# ---------- exact derivative fractions ----------

def cheb_U_coeffs(n):
    """Power-basis coefficients of U_0..U_{n-1}."""
    U = [[F(1)], [F(0), F(2)]]
    while len(U) < n:
        U.append(lp_add(lp_mul([F(0), F(2)], U[-1]), lp_smul(F(-1), U[-2])))
    return U[:n]


def finite_U(cs):
    """sum_k cs[k]/1e8 * U_k(x)  (derivative of sum u_k T_k/k)."""
    out = []
    for k, (c, Uk) in enumerate(zip(cs, cheb_U_coeffs(len(cs)))):
        out = lp_add(out, lp_smul(F(c, E8), Uk))
    return out


def finite_pow(cs):
    """sum_k cs[k]/1e8 * x^k  (derivative of sum u_k x^k / k)."""
    return [F(c, E8) for c in cs]


def tail_T_frac(z):
    """Re[r z / (1 - 2 x z + z^2)] as (num, den) for r = rr + i ri (num depends on r)."""
    zr, zi, rr, ri = z
    P = rr * zr - ri * zi            # Re(r z)
    Q = rr * zi + ri * zr            # Im(r z)
    if zi == 0 and ri == 0:
        return [P], [1 + zr * zr, -2 * zr]
    al = 1 + zr * zr - zi * zi       # Re(1 + z^2)
    be = 2 * zr * zi                 # Im(1 + z^2)
    # w = (al - 2 zr x) + i (be - 2 zi x);  Re[(P + iQ) conj w] = P(al - 2 zr x) + Q(be - 2 zi x)
    num = [P * al + Q * be, -2 * (P * zr + Q * zi)]
    den = lp_add(lp_mul([al, -2 * zr], [al, -2 * zr]), lp_mul([be, -2 * zi], [be, -2 * zi]))
    return num, den


def tail_S_frac(z):
    """Re[r z / (1 - x z)]."""
    zr, zi, rr, ri = z
    P = rr * zr - ri * zi
    Q = rr * zi + ri * zr
    if zi == 0 and ri == 0:
        return [P], [F(1), -zr]
    # 1 - x z = (1 - zr x) - i zi x ; Re[(P + iQ)((1 - zr x) + i zi x)] = P(1 - zr x) - Q zi x
    num = [P, -(P * zr + Q * zi)]
    den = lp_add(lp_mul([F(1), -zr], [F(1), -zr]), lp_mul([F(0), zi], [F(0), zi]))
    return num, den


def frac_sum(fracs):
    N, D = [F(0)], [F(1)]
    for n, d in fracs:
        N = lp_add(lp_mul(N, d), lp_mul(n, D))
        D = lp_mul(D, d)
    return N, D


def row_fracs(P, V):
    fr = [([F(19, 48)], [F(0), F(1)]),
          ([F(-1, 12)], [F(1), F(-1)]),
          ([F(0), F(-65, 24)], [F(1), F(0), F(1)]),
          (lp_add(lp_smul(F(-4), finite_U(P.cs)), lp_smul(F(-1), finite_pow(V.cs))), [F(1)])]
    for z in P.tail:
        n, d = tail_T_frac(z)
        fr.append((lp_smul(F(-4), n), d))
    for z in V.tail:
        n, d = tail_S_frac(z)
        fr.append((lp_smul(F(-1), n), d))
    return fr


def col_fracs(V):
    fr = [([F(7, 48)], [F(0), F(1)]),
          ([F(-1, 12)], [F(1), F(-1)]),
          (lp_smul(F(2), finite_U(V.cs)), [F(1)])]
    for z in V.tail:
        n, d = tail_T_frac(z)
        fr.append((lp_smul(F(2), n), d))
    return fr


# ---------- float evaluation ----------

def T_field(u, x):
    x = np.asarray(x, dtype=float)
    out = np.zeros_like(x)
    Tkm, Tk = np.ones_like(x), x.copy()
    for k in range(1, len(u.cs) + 1):
        out += u.cs[k - 1] / E8 * Tk / k
        Tkm, Tk = Tk, 2 * x * Tk - Tkm
    for zr, zi, rr, ri in u.tail:
        z = complex(zr, zi); r = complex(rr, ri)
        out += (-0.5 * r * np.log(1 - 2 * x * z + z * z)).real
    return out


def S_field(u, x):
    x = np.asarray(x, dtype=float)
    out = np.zeros_like(x)
    for k in range(1, len(u.cs) + 1):
        out += u.cs[k - 1] / E8 * x ** k / k
    for zr, zi, rr, ri in u.tail:
        z = complex(zr, zi); r = complex(rr, ri)
        out += (-r * np.log(1 - x * z)).real
    return out


def X_field(P, V, x):
    x = np.asarray(x, dtype=float)
    W = 19 / 48 * np.log(np.abs(x)) + 1 / 12 * np.log(1 - x) - 65 / 48 * np.log(1 + x * x)
    return W - 4 * T_field(P, x) - S_field(V, x)


def Y_field(V, s):
    s = np.asarray(s, dtype=float)
    return 7 / 48 * np.log(s) + 1 / 12 * np.log(1 - s) + 2 * T_field(V, s)


def norm_sq(u, J=20000):
    k = np.arange(1, J + 1)
    c = np.array([u.coeff(int(j)) for j in k]) if J <= 2000 else None
    if c is None:
        c = np.zeros(J)
        c[:len(u.cs)] = np.array(u.cs) / E8
        for zr, zi, rr, ri in u.tail:
            c += (complex(rr, ri) * complex(zr, zi) ** k).real
    return float(np.sum(c * c / k))
