"""Exact Python mirror of the Lean bank checker `BankShared.Check` (lane C1L, 28 Oct 2026).

It mirrors, operation by operation, the Lean definitions
  Expr / evalN / err / affineOn        (Check/Expr.lean, Check/Affine.lean)
  Cond / etaLo / exactL / exactR      (Check/Cond.lean)
  pieceOK (K0-K4), check (D1-D6)     (Check/Cover.lean, Check/Bank.lean)
and adds what Lean does not need: the certificate search (subdivision points, strip branches).
Reference: outputs/Compatibility programme/automatic-banks-2026-10-28/C1/{PAPER.md, checker.py}.
All arithmetic is fractions.Fraction."""
from fractions import Fraction as F
import math

# ------------------------------------------------------------------------------------ expressions
# ('r',) ('p',) ('m',) ('k',) ('c', n) ('add', a, b) ('smul', n, a) ('tsub', a, b) ('min', a, b)
# ('max', a, b) ('dist', a) ('ap',) ('sp',)
R, P, M, K, AP, SP = ('r',), ('p',), ('m',), ('k',), ('ap',), ('sp',)
def C(n): return ('c', n)
def add(a, b): return ('add', a, b)
def smul(n, a): return ('smul', n, a)
def tsub(a, b): return ('tsub', a, b)
def mn(a, b): return ('min', a, b)
def mx(a, b): return ('max', a, b)
def dist(a): return ('dist', a)

def evalN(e, r, p, m, k):
    t = e[0]
    if t == 'r': return r
    if t == 'p': return p
    if t == 'm': return m
    if t == 'k': return k
    if t == 'c': return e[1]
    if t == 'add': return evalN(e[1], r, p, m, k) + evalN(e[2], r, p, m, k)
    if t == 'smul': return e[1] * evalN(e[2], r, p, m, k)
    if t == 'tsub': return max(evalN(e[1], r, p, m, k) - evalN(e[2], r, p, m, k), 0)
    if t == 'min': return min(evalN(e[1], r, p, m, k), evalN(e[2], r, p, m, k))
    if t == 'max': return max(evalN(e[1], r, p, m, k), evalN(e[2], r, p, m, k))
    if t == 'dist':
        x = evalN(e[1], r, p, m, k) % p
        return min(x, p - x)
    if t == 'ap': return p * (r // p)
    if t == 'sp': return r % p
    raise ValueError(e)

def err(e, eps):
    """Lemma 1 error constant E(e) (Check/Expr.lean `Expr.err`)."""
    t = e[0]
    if t in ('r', 'p', 'ap', 'sp'): return F(0)
    if t == 'm': return F(1, 2)
    if t == 'k': return eps
    if t == 'c': return F(e[1])
    if t in ('add', 'tsub'): return err(e[1], eps) + err(e[2], eps)
    if t == 'smul': return e[1] * err(e[2], eps)
    if t in ('min', 'max'): return max(err(e[1], eps), err(e[2], eps))
    if t == 'dist': return err(e[1], eps)
    raise ValueError(e)

def lv(l, x): return l[0] + l[1] * x

def aff(e, al, ka, u, v):
    """Check/Affine.lean `affineOn`: the line (c0, c1) of the homogenised profile on (u, v], or None."""
    t = e[0]
    if t == 'r': return (F(1), F(0))
    if t == 'p': return (F(0), F(1))
    if t == 'm': return (al, F(0))
    if t == 'k': return (F(0), ka)
    if t == 'c': return (F(0), F(0))
    if t == 'add':
        a = aff(e[1], al, ka, u, v); b = aff(e[2], al, ka, u, v)
        return None if a is None or b is None else (a[0] + b[0], a[1] + b[1])
    if t == 'smul':
        a = aff(e[2], al, ka, u, v)
        return None if a is None else (e[1] * a[0], e[1] * a[1])
    if t in ('tsub', 'min', 'max'):
        a = aff(e[1], al, ka, u, v); b = aff(e[2], al, ka, u, v)
        if a is None or b is None: return None
        d = (a[0] - b[0], a[1] - b[1])
        ge = lv(d, u) >= 0 and lv(d, v) >= 0
        le = lv(d, u) <= 0 and lv(d, v) <= 0
        if t == 'tsub':
            return d if ge else ((F(0), F(0)) if le else None)
        if t == 'min':
            return a if le else (b if ge else None)
        return a if ge else (b if le else None)
    if t == 'dist':
        a = aff(e[1], al, ka, u, v)
        if a is None: return None
        w = (u + v) / 2
        n = math.floor(lv(a, w) / w + F(1, 2))
        d = (a[0], a[1] - n)
        if not (2 * lv(d, u) <= u and -u <= 2 * lv(d, u) and 2 * lv(d, v) <= v and -v <= 2 * lv(d, v)):
            return None
        if lv(d, u) >= 0 and lv(d, v) >= 0: return d
        if lv(d, u) <= 0 and lv(d, v) <= 0: return (-d[0], -d[1])
        return None
    if t in ('ap', 'sp'):
        n = math.floor(1 / v)
        if not ((n + 1) * u >= 1): return None
        return (F(0), F(n)) if t == 'ap' else (F(1), F(-n))
    raise ValueError(e)

def split_point(e, al, ka, u, v):
    """a breakpoint of the profile strictly inside (u, v) at which `aff` fails (Python only)."""
    t = e[0]
    kids = {'add': [1, 2], 'smul': [2], 'tsub': [1, 2], 'min': [1, 2], 'max': [1, 2], 'dist': [1]}.get(t, [])
    for i in kids:
        if aff(e[i], al, ka, u, v) is None:
            return split_point(e[i], al, ka, u, v)
    if t in ('tsub', 'min', 'max'):
        a = aff(e[1], al, ka, u, v); b = aff(e[2], al, ka, u, v)
        d = (a[0] - b[0], a[1] - b[1])
        x = -d[0] / d[1]
        assert u < x < v, (e, u, v, x)
        return x
    if t == 'dist':
        a = aff(e[1], al, ka, u, v)
        # breakpoints of theta * ||X/theta||: X = n theta and X = (n + 1/2) theta
        cands = []
        for n2 in range(-400, 400):
            h = F(n2, 2)
            if a[1] - h != 0:
                x = -a[0] / (a[1] - h)
                if u < x < v: cands.append(x)
        assert cands, (e, u, v)
        return min(cands, key=lambda x: abs(x - (u + v) / 2))
    if t in ('ap', 'sp'):
        n = math.floor(1 / v)
        x = F(1, n + 1)
        assert u < x < v
        return x
    raise AssertionError(('no split', e, u, v))

def subdivide(e, al, ka, u, v):
    """interior points s < x1 < ... < t such that `aff` succeeds on every (x_i, x_{i+1}]."""
    if aff(e, al, ka, u, v) is not None:
        return []
    x = split_point(e, al, ka, u, v)
    return subdivide(e, al, ka, u, x) + [x] + subdivide(e, al, ka, x, v)

# ------------------------------------------------------------------------------------ conditions
# (cr, cp, cm, ck, c1, strict):  L = cr r + cp p + cm m + ck k + c1,  L > 0 (strict) or L >= 0.
def ell(c, al, ka): return (c[0] + c[2] * al, c[1] + c[3] * ka)

def eta_lo(c, q):
    """(lower end, closed) of eta = cm e_m + ck e_k + c1, e_m in [-1/2, 1/2), e_k in [1/q, 1-1/q]."""
    cm, ck, c1 = c[2], c[3], c[4]
    lo = cm * (F(-1, 2) if cm >= 0 else F(1, 2)) + ck * (F(1, q) if ck >= 0 else 1 - F(1, q)) + c1
    return lo, cm >= 0

def odd(c): return c[0] % 2 == 0 and c[2] % 2 == 0 and c[3] % 2 == 0 and (c[1] + c[4]) % 2 == 1

def exactL(c, q):
    lo, _ = eta_lo(c, q)
    if c[5]: return lo >= 0 or (lo >= -1 and odd(c))
    return lo >= -1

def exactR(c, q):
    lo, cl = eta_lo(c, q)
    gtm1 = lo > -1 or (lo == -1 and not cl)
    gt0 = lo > 0 or (lo == 0 and not cl)
    if c[5]: return gt0 or (gtm1 and odd(c))
    return gtm1

# ------------------------------------------------------------------------------------ crude constant
def lgF(n, fuel=64):
    out = 0
    while fuel > 0 and n >= 2:
        n //= 2; out += 1; fuel -= 1
    return out

def kcrude(Rq, cF):
    Rn = max(math.ceil(Rq), 2)
    L = lgF(14 * Rn)
    assert 14 * Rn < 2 ** (L + 1)
    return 2 * Rn * (3 * L + cF)

# ------------------------------------------------------------------------------------ piece check
def piece_ok(P, cert, cat, q, al, ka, depth, cF, Pbad, why=None):
    """Check/Cover.lean `pieceOK`.  P = (s, t, a, b, C); cert = (bi, cuts, strips) with strips a list of
    (left: bool, yi, w).  Returns (ok, R, need)."""
    s, t, a, b, Cc = P
    bi, cuts, strips = cert
    def bad(msg):
        if why is not None: why.append(msg)
        return (False, None, None)
    if not (0 < s < t and a + b * s >= 0 and a + b * t >= 0 and Cc >= 0): return bad('K0')
    if bi >= len(cat): return bad('index')
    tau, conds, deb = cat[bi]
    eps = 1 - F(1, q)
    # K1 and the binding classification
    R = max(q * (2 + 2 * al) / (s * s), F(Pbad) / s, F(1))
    needL = needR = False
    for c in conds:
        l = ell(c, al, ka)
        ls, lt = lv(l, s), lv(l, t)
        if ls < 0 or lt < 0: return bad('K1')
        if ls == 0 or lt == 0:
            if l[1] == 0: return bad('K1 flat')
            if ls == 0 and not exactL(c, q): needL = True
            if lt == 0 and not exactR(c, q): needR = True
        else:
            R = max(R, (1 - eta_lo(c, q)[0]) / min(ls, lt))
    # K2
    pts = [s] + list(cuts) + [t]
    for u, v in zip(pts, pts[1:]):
        if not (u < v): return bad('K2 order')
        ln = aff(tau, al, ka, u, v)
        if ln is None: return bad(f'K2 aff ({u},{v}]')
        if lv(ln, u) > a + b * u or lv(ln, v) > a + b * v: return bad(f'K2 line ({u},{v}]')
    need = err(tau, eps) + deb * depth
    # K3 strips
    for left, e, want in ((True, s, needL), (False, t, needR)):
        if not want: continue
        st = [x for x in strips if x[0] == left]
        if not st: return bad('K3 missing strip')
        _, yi, w = st[0]
        if yi >= len(cat) or not (0 < w): return bad('K3 strip data')
        ty, cy, dy = cat[yi]
        V = F(0)
        for c in conds:
            l = ell(c, al, ka)
            if lv(l, e) == 0:
                V = max(V, (1 - eta_lo(c, q)[0]) / abs(l[1]))
        for c in cy:
            l = ell(c, al, ka)
            le = lv(l, e)
            if not (le > 0): return bad('K3 strip branch not interior')
            R = max(R, 2 * (1 - eta_lo(c, q)[0]) / le, 2 * V * abs(l[1]) / le)
        if left:
            ln = aff(ty, al, ka, e, e + w)
        else:
            if not (w < e): return bad('K3 w')
            ln = aff(ty, al, ka, e - w, e)
        if ln is None: return bad('K3 strip aff')
        if lv(ln, e) > a + b * e: return bad('K3 strip value')
        R = max(R, V / w)
        need = max(need, err(ty, eps) + dy * depth + (abs(b) + abs(ln[1])) * V)
    need = max(need, F(kcrude(R, cF)))
    if Cc < need: return bad(f'K4 C={Cc} need={need}')
    return (True, R, need)

# ------------------------------------------------------------------------------------ bank check
def jOf(q, a, c):
    for x in range(q):
        if (x * c) % q == a % q:
            return x
    return None

def mass(alpha0, t1, pieces):
    return alpha0 * t1 + sum(a * (t - s) + b * (t * t - s * s) / 2 for (s, t, a, b, _), _ in pieces)

def check(D, why=None):
    """Check/Bank.lean `check`.  D: dict with q, M, al, members, depth, cF, Pbad, alpha0, tau, Lam, alpha0b, t0,
    cat (list of (tau, conds, debit)), iD6, tmpls {j: (t1, [(piece, cert)])}."""
    ok = True
    def bad(msg):
        nonlocal ok
        ok = False
        if why is not None: why.append(msg)
    q, Mm, al = D['q'], D['M'], D['al']
    if not (q >= 2 and Mm % q == 0 and D['Pbad'] >= q and D['Pbad'] >= 2): bad('params')
    if D['cat'][D['iD6']] != D6: bad('D6 index')
    for a in D['members']:
        if not (0 < a < q and math.gcd(a, q) == 1): bad('member')
    # D1 class map and D6 hmass (per member, as contentConstant needs)
    units = [c for c in range(Mm) if math.gcd(c, Mm) == 1]
    for a in D['members']:
        tot = F(0)
        for c in units:
            j = jOf(q, a, c)
            if j is None or j not in D['tmpls']:
                bad(f'D1 a={a} c={c}'); continue
            t1, pcs = D['tmpls'][j]
            tot += mass(D['alpha0'], t1, pcs)
        if tot != D['Lam'] * len(units): bad(f'D6 a={a} {tot / len(units)} != {D["Lam"]}')
    # D3
    if not (D['alpha0'] >= D['alpha0b'] and D['alpha0'] >= 0): bad('D3 alpha0')
    maxR, maxN = F(0), F(0)
    for j, (t1, pcs) in D['tmpls'].items():
        ka = F(j, q)
        if not (0 < t1 <= D['t0']): bad(f'D3 t1 j={j}')
        cur = t1
        for P, cert in pcs:
            if P[0] != cur: bad(f'D2 chain j={j} at {P[0]}')
            cur = P[1]
            w = []
            res = piece_ok(P, cert, D['cat'], q, al, ka, D['depth'], D['cF'], D['Pbad'], w)
            if not res[0]:
                bad(f'D5 j={j} piece {P[:2]}: {w}')
            else:
                maxR, maxN = max(maxR, res[1]), max(maxN, res[2])
        tend = cur
        if not (ka * tend >= 1 + 2 * al and tend >= q * (1 + 2 * al) and 2 * tend >= D['Pbad']):
            bad(f'D4 tail j={j}')
        if not (tend <= D['tau']): bad(f'D4 tail_lt j={j}')
    return ok, dict(max_R_P=maxR, max_C_needed=maxN)

# ------------------------------------------------------------------------------------ the generic catalogue
COND = {
    'p<=r':   (1, -1, 0, 0, 0, False),
    'r<p':    (-1, 1, 0, 0, 0, True),
    '2m<p':   (0, 1, -2, 0, 0, True),
    '2m<=p':  (0, 1, -2, 0, 0, False),
    'k<=r':   (1, 0, 0, -1, 0, False),
    'r<=k':   (-1, 0, 0, 1, 0, False),
    'N<=p':   (-1, 1, -2, 0, 0, False),
    'N<=2p':  (-1, 2, -2, 0, 0, False),
    'r<p+k':  (-1, 1, 0, 1, 0, True),
    'N<=p+k': (-1, 1, -2, 1, 0, False),
    'p<r+m':  (1, -1, 1, 0, 0, True),
    'm<p':    (0, 1, -1, 0, 0, True),
}
N_ = add(R, smul(2, M))
two = lambda x: smul(2, x)
D1 = (two(add(R, M)), [], 0)
D1x = (tsub(add(two(R), two(M)), dist(M)), [], 0)
_u0 = tsub(add(K, P), R)
D2 = (add(add(two(tsub(R, _u0)), two(M)), mn(_u0, two(M))), [COND['2m<p'], COND['p<=r'], COND['k<=r']], 0)
D3 = (add(two(R), M), [COND['2m<p'], COND['p<=r']], 0)
D45 = (add(add(two(tsub(R, K)), two(M)), tsub(two(M), tsub(P, R))), [COND['r<p']], 0)
D6 = (tsub(two(M), tsub(K, R)), [COND['N<=p'], COND['r<=k']], 0)
_w = tsub(add(P, K), R)
LP1 = (tsub(add(add(two(tsub(R, tsub(K, tsub(R, P)))), two(M)), mn(two(M), _w)), tsub(mn(_w, two(M)), M)),
       [COND['N<=2p'], COND['p<=r'], COND['r<p+k'], COND['k<=r']], 1)
LP2 = (tsub(add(add(two(tsub(R, K)), two(M)), tsub(two(M), tsub(P, R))), tsub(M, tsub(P, R))),
       [COND['r<p'], COND['k<=r'], COND['N<=p+k'], COND['p<r+m']], 1)
def _W(base, lo, hi):      # |[r, N) cap [base + lo, base + hi)|
    return tsub(mn(N_, add(base, hi) if base is not None else hi), mx(R, add(base, lo) if base is not None else lo))
_nsq = tsub(mn(R, K), tsub(N_, P))
_W00 = tsub(mn(N_, K), R)                                  # W(0,0)
_W10 = tsub(mn(N_, add(P, K)), mx(R, P))                    # W(1,0)
_Wh0 = tsub(mn(N_, add(AP, K)), mx(R, AP))                  # W(h,0)
_Wh1 = tsub(mn(N_, add(AP, P)), mx(R, add(AP, K)))          # W(h,1)
_AP1 = add(AP, P)
_Wh10 = tsub(mn(N_, add(_AP1, K)), mx(R, _AP1))             # W(h+1,0)
_Wh11 = tsub(mn(N_, add(_AP1, P)), mx(R, add(_AP1, K)))     # W(h+1,1)
_kap = add(M, _nsq)
_WD0 = add(add(_W00, _W10), two(_nsq))
RANK = (tsub(two(add(R, M)), mx(mx(_kap, _WD0), mx(mx(_Wh0, _Wh1), mx(_Wh10, _Wh11)))), [COND['2m<p']], 0)

def window(n0, n1):
    """M3D window between the n0-th and (n0+1)-th multiple of p and between the k-cuts k + (n1-1) p and
    k + n1 p (n1 = 0: below k):  2r + (2m - (b - a))."""
    lo_k = R if n1 == 0 else add(K, smul(n1 - 1, P))
    a = mx(mx(tsub(N_, P), R), mx(smul(n0, P), lo_k))
    b = mn(mn(N_, add(R, P)), mn(smul(n0 + 1, P), add(K, smul(n1, P))))
    return (add(two(R), tsub(two(M), tsub(b, a))), [COND['m<p']], 0)

BASE = [('T.D1', D1), ('T.D1x', D1x), ('T.D2', D2), ('T.D3', D3), ('T.D45', D45), ('T.D6', D6),
        ('LP1', LP1), ('LP2', LP2), ('R', RANK)]

# ------------------------------------------------------------------------------------ the Lean form of pieceOK
def strip_V(conds, al, ka, q, e):
    V = F(0)
    for c in conds:
        l = ell(c, al, ka)
        if lv(l, e) == 0:
            V = max(V, (1 - eta_lo(c, q)[0]) / abs(l[1]))
    return V

def piece_ok_lean(P, cert, cat, q, al, ka, depth, cF, Pbad):
    """Check/Cover.lean `pieceOK`, literally: cert = (bi, cuts, strips [(left, yi, w, V)], R)."""
    s, t, a, b, Cc = P
    bi, cuts, strips, Rr = cert
    if bi >= len(cat): return False
    tau, conds, deb = cat[bi]
    eps = 1 - F(1, q)
    if not (0 < s and s < t and 0 <= a + b * s and 0 <= a + b * t and 0 <= Cc): return False
    for c in conds:
        l = ell(c, al, ka); ls, lt = lv(l, s), lv(l, t)
        if not (0 <= ls and 0 <= lt and ((ls != 0 and lt != 0) or l[1] != 0)): return False
    pts = [s] + list(cuts) + [t]
    for u, v in zip(pts, pts[1:]):
        if not u < v: return False
        ln = aff(tau, al, ka, u, v)
        if ln is None or not (lv(ln, u) <= a + b * u and lv(ln, v) <= a + b * v): return False
    if not (F(q) * (2 + 2 * al) / (s * s) <= Rr and F(Pbad) / s <= Rr and 1 <= Rr): return False
    for c in conds:
        l = ell(c, al, ka); ls, lt = lv(l, s), lv(l, t)
        if not (ls == 0 or lt == 0 or (1 - eta_lo(c, q)[0]) / min(ls, lt) <= Rr): return False
    def strip_ok(e, st):
        left, yi, w, V = st
        if yi >= len(cat): return False
        ty, cy, dy = cat[yi]
        if not (0 < w and (left or w < e)): return False
        for c in conds:
            l = ell(c, al, ka)
            if not (lv(l, e) != 0 or (1 - eta_lo(c, q)[0]) / abs(l[1]) <= V): return False
        for c in cy:
            l = ell(c, al, ka); le = lv(l, e)
            if not (0 < le and 2 * (1 - eta_lo(c, q)[0]) / le <= Rr and 2 * V * abs(l[1]) / le <= Rr): return False
        if not (V / w <= Rr): return False
        ln = aff(ty, al, ka, e, e + w) if left else aff(ty, al, ka, e - w, e)
        if ln is None: return False
        return lv(ln, e) <= a + b * e and err(ty, eps) + dy * depth + (abs(b) + abs(ln[1])) * V <= Cc
    needL = any(lv(ell(c, al, ka), s) == 0 and not exactL(c, q) for c in conds)
    needR = any(lv(ell(c, al, ka), t) == 0 and not exactR(c, q) for c in conds)
    if needL and not any(st[0] and strip_ok(s, st) for st in strips): return False
    if needR and not any((not st[0]) and strip_ok(t, st) for st in strips): return False
    if not (err(tau, eps) + deb * depth <= Cc): return False
    Rn = max(math.ceil(Rr), 2)
    L = lgF(14 * Rn)
    return 14 * Rn < 2 ** (L + 1) and 2 * Rn * (3 * L + cF) <= Cc

# ------------------------------------------------------------------------------------ the UF branch S (Check/UF.lean)
def _eB(kap): return add(AP, P) if kap else AP
def _eL(zeta): return K if zeta else C(0)
def _eU(zeta): return tsub(P, C(1)) if zeta else tsub(K, C(1))
def _eUb(kap, zeta): return mn(_eU(zeta), tsub(SP, C(1))) if kap else _eU(zeta)
def _eOvl(a, b): return tsub(mn(N_, add(b, C(1))), mx(R, a))
def _eBeta(w0, w1): return add(add(_eOvl(w0, w1), _eOvl(add(w0, P), add(w1, P))), _eOvl(tsub(w0, P), tsub(w1, P)))
def _eCB(t0, tv, w0):
    W = tsub(mn(add(tv, C(1)), N_), t0)
    return tsub(two(add(R, M)), add(add(M, tsub(W, M)),
                                    tsub(tsub(W, M), tsub(P, add(tsub(add(tv, C(1)), w0), tsub(two(M), _eBeta(w0, tv)))))))
def tCand(kap, zeta):
    B, L = _eB(kap), _eL(zeta)
    return _eCB(mx(R, add(B, L)), add(B, _eUb(kap, zeta)), add(B, L))
TS = mn(mn(tCand(False, False), tCand(False, True)), mn(tCand(True, False), tCand(True, True)))
COND['1<=m'] = (0, 0, 1, 0, -1, False)
UFS = (TS, [COND['2m<=p'], COND['1<=m']], 1)


# ------------------------------------------------------------------------------------ LP2 widened and the prefix branches
# Check/LP2W.lean `brLP2w`: tLP2 with the condition N <= p + k replaced by N <= 2p (same expression, debit 1).
LP2W = (LP2[0], [COND['r<p'], COND['k<=r'], COND['N<=2p'], COND['p<r+m']], 1)
BASE_W = [(n, (LP2W if n == 'LP2' else b)) for n, b in BASE]

def _eNn(n): return add(R, smul(2, tsub(M, smul(n, P))))

def prefix(n, j0, j1):
    """Check/Prefix.lean `brPre n j0 j1`: the window bound of Theorem 1 at the strip n, price
    2r + (2m - (hi - lo)), no conditions, debit 0."""
    en = _eNn(n)
    lo_k = R if j1 == 0 else add(AP, add(K, smul(j1 - 1, P)))
    lo = mx(mx(tsub(en, P), R), mx(add(AP, smul(j0, P)), lo_k))
    hi = mn(mn(en, add(R, P)), mn(add(AP, smul(j0 + 1, P)), add(AP, add(K, smul(j1, P)))))
    return (add(smul(2, R), tsub(smul(2, M), tsub(hi, lo))), [], 0)

def pres_list(nmax):
    """all (n, j0, j1) with 1 <= n <= nmax, j0 < 2, j1 < 3 (the Lean `bankPres`)."""
    return [(n, j0, j1) for n in range(1, nmax + 1) for j0 in range(2) for j1 in range(3)]
