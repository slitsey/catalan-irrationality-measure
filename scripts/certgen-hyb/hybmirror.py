# Exact integer mirror of the Lean SigmaHyb checks (HMacro.lean): hybrid sigma300 + lambda, rho = 1/1024, r0 = 7/50.
import json, math, sys, os, re, bisect
sys.set_int_max_str_digits(0)
sys.path.insert(0, 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-thmA/scripts/certgen-p6')
from fractions import Fraction as F
from tables import tup, tlo, alo, JM
import numpy as np

ROOT = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/'
LEG = ROOT + 'work/catalan-thmA/CatalanLambda/Cert/'
R0 = F(7, 50)
RHO2 = 2 ** 60
Z = 2 ** 40
P = 2 ** 64
PILO = F(314159265358979323846, 10 ** 20)
L2UP = F(6931471808, 10 ** 10)
LAMFILE = ROOT + 'outputs/claude-2026-10-16/GN-audit-GG/lam4_80_20_0.42_1.npz'

def logUpS(N):
    L = N.bit_length() - 1
    i = ((N << 8) >> L) - 256
    e = (L - 80) * (tup[256] if L >= 80 else tlo[256])
    f0 = 256 + i
    R = ((N << 72) + (f0 << L) - 1) // (f0 << L) - P
    return e + tup[i] + R
def logLoS(N):
    L = N.bit_length() - 1
    i = ((N << 8) >> L) - 256
    e = (L - 80) * (tlo[256] if L >= 80 else tup[256])
    f1 = 257 + i
    c = ((f1 << (L + 56)) + N - 1) // N
    return e + tlo[i + 1] + P - c

def theta(vlo):
    assert vlo >= 0
    j = min(math.floor(vlo * 256), JM)
    return F(alo[j], P) + (0 if j == JM else (vlo - F(j, 256)) / (1 + F(j + 1, 256) ** 2))

def load_sigma():
    t = open(LEG + 'SigmaSorted.lean', encoding='utf-8').read()
    pts = [(int(a), int(b), int(c)) for a, b, c in re.findall(r'\(\(?(-?\d+)[^,]*,\s*\(?(-?\d+)[^,]*,\s*(\d+)\)', t)]
    assert len(pts) == 300 and sum(p[2] for p in pts) == 2 ** 32
    return pts

def load_lam(lamfile=LAMFILE):
    z = np.load(lamfile); cs, cr, m = z['cs'], z['cr'], z['m']; n1 = len(cs)
    PB = 2 ** 24; MB = 2 ** 32
    mi = [int(round(v * MB)) for v in m[:n1]] + [int(round(v / 2 * MB)) for v in m[n1:]]
    tot = sum(mi[:n1]) + 2 * sum(mi[n1:]); target = MB // 8
    k = int(np.argmax(mi[:n1])); mi[k] += target - tot
    assert sum(mi[:n1]) + 2 * sum(mi[n1:]) == target and min(mi) >= 0
    Lm = []
    for j, c in enumerate(cs):
        if mi[j] != 0: Lm.append((int(round(c.real * PB)) << 16, 0, mi[j]))
    for j, c in enumerate(cr):
        q = mi[n1 + j]
        if q != 0:
            X = int(round(c.real * PB)) << 16; Y = int(round(c.imag * PB)) << 16
            Lm.append((X, Y, q)); Lm.append((X, -Y, q))
    assert sum(p[2] for p in Lm) == 2 ** 29
    return sorted(Lm, key=lambda p: (p[0], p[1]))

SIG = load_sigma()
SIG.sort(key=lambda p: (p[0], p[1]))
LAM = load_lam()
HYB = sorted(SIG + LAM, key=lambda p: (p[0], p[1]))

class Lst:
    def __init__(self, pts):
        self.pts = pts; self.KX = [p[0] for p in pts]

def near_sum(box, near):
    xlo, xhi, ylo, yhi = box; t = 0
    for X, Y, n in near:
        dx = max(abs(xlo - X), abs(xhi - X)); dy = max(abs(ylo - Y), abs(yhi - Y))
        t += n * logUpS(dx * dx + dy * dy + RHO2)
    return t
def far_data(x0, y0, far):
    L = Ax = Ex = Ay = Ey = H = 0
    for X, Y, n in far:
        dx = x0 - X; dy = y0 - Y
        q0 = dx * dx + dy * dy + RHO2
        lo = 2 ** 100 // q0
        L += n * logUpS(q0); Ax += n * dx * lo; Ex += n * abs(dx); Ay += n * dy * lo; Ey += n * abs(dy); H += n * (lo + 1)
    return (L, Ax, Ex, Ay, Ey, H)
def maxprod(gl, gh, a, b): return max(gl * a, gl * b, gh * a, gh * b)
def sig_lb(lst, x0, y0, i0, i1, fd, box):
    xlo, xhi, ylo, yhi = box
    L, Ax, Ex, Ay, Ey, H = fd
    ulo, uhi, vlo, vhi = xlo - x0, xhi - x0, ylo - y0, yhi - y0
    lin = 2 * (maxprod(Ax - Ex, Ax + Ex, ulo, uhi) + maxprod(Ay - Ey, Ay + Ey, vlo, vhi))
    quad = H * (max(ulo * ulo, uhi * uhi) + max(vlo * vlo, vhi * vhi))
    return F(-near_sum(box, lst.pts[i0:i1]), 2 ** 97) - F(L, 2 ** 97) - F(lin + quad, 2 ** 133)
def sig_flat(lst, box):
    return F(-near_sum(box, lst.pts), 2 ** 97)

def ubUp(xlo, xhi, ylo, yhi):
    assert xhi < 0 and xlo <= xhi and ylo >= 0
    L1 = F(logUpS(xlo * xlo + yhi * yhi), P)
    A = F(1, 2) * max(F(-xhi, Z) * L1, F(-xlo, Z) * L1)
    l = F(logLoS((Z - xhi) ** 2 + ylo * ylo), P)
    B = -F(1, 2) * min(F(Z - xhi, Z) * l, F(Z - xlo, Z) * l)
    den = xlo * xlo + yhi * yhi - xlo * Z
    th = theta(F(ylo * Z, den))
    C = -min(F(ylo, Z) * th, F(yhi, Z) * th)
    return 1 + A + B + C
def uexUp(xlo, xhi, ylo, yhi):
    return F(1, 8) * ubUp(4 * xlo - 2 ** 42, 4 * xhi - 2 ** 42, 4 * ylo, 4 * yhi) + L2UP / 4
def boxLBg(Ls, b):
    xlo, xhi, ylo, yhi = b
    return Ls - ubUp(*b) + F(999, 1000) * PILO * F(ylo, Z)
def boxLBH(Ls, b): return boxLBg(Ls, b) - uexUp(*b)
def hLB(Ls, b): return Ls - uexUp(*b)

# line (real axis [0,1])
from math import isqrt
def l_lo(N): return F(logLoS(N), 2 ** 65)
def l_up(N): return F(logUpS(N), 2 ** 65)
def ut_A(xlo, xhi):
    assert xhi <= 0 and xlo >= -Z
    if xhi == 0: F1 = F(0)
    else:
        T1 = -xhi; T2 = -xlo; a = l_lo(T1 * T1); b = l_up(T2 * T2)
        F1 = max(F(T1, Z) * a, F(T1, Z) * b, F(T2, Z) * a, F(T2, Z) * b)
    S1 = F(Z - xhi, Z); Ll = l_lo((Z - xhi) ** 2)
    return 1 + F1 - S1 * Ll
def tlogUB(t1, t2):
    if t1 == 0: return 2 * F(isqrt(t2 * Z) + 1, Z)
    a = l_lo(t1 * t1); b = l_up(t2 * t2)
    return max(-F(t1, Z) * a, -F(t1, Z) * b, -F(t2, Z) * a, -F(t2, Z) * b)
def ut_B(xlo, xhi):
    assert 0 <= xlo <= xhi <= Z
    return 1 + tlogUB(xlo, xhi) + tlogUB(Z - xhi, Z - xlo)
def uexAxisUp(xlo, xhi):
    if xhi == Z:
        assert 4 * xlo - 2 ** 42 >= -Z
        u = ut_A(4 * xlo - 2 ** 42, 0)
    else:
        u = ubUp(4 * xlo - 2 ** 42, 4 * xhi - 2 ** 42, 0, 0)
    return F(1, 8) * u + L2UP / 4
def lLB(lst, x0, y0, i0, i1, fd, xlo, xhi):
    return sig_lb(lst, x0, y0, i0, i1, fd, (xlo, xhi, 0, 0)) - ut_B(xlo, xhi) - uexAxisUp(xlo, xhi)

DS = [0.004, 0.008, 0.016, 0.03, 0.06, 0.12, 0.25, 0.5, 1, 10]
def window(lst, x0, Dd):
    return bisect.bisect_left(lst.KX, x0 - int(Dd * Z)), bisect.bisect_right(lst.KX, x0 + int(Dd * Z))

def macro_choose(lst, boxes, lbfun, ok, costw=2.0, DSL=DS, y0=None):
    """boxes: list of (xlo,xhi,ylo,yhi). ok(i, lb) -> bool. lbfun(Ls, box)->bound. Returns (cost,x0,y0,i0,i1,lbs) or None."""
    xs = min(b[0] for b in boxes); xe = max(b[1] for b in boxes); ys = min(b[2] for b in boxes); ye = max(b[3] for b in boxes)
    x0 = (xs + xe) // 2; yy = (ys + ye) // 2 if y0 is None else y0
    for Dd in DSL:
        i0, i1 = window(lst, x0, Dd)
        far = lst.pts[:i0] + lst.pts[i1:]
        fd = far_data(x0, yy, far)
        lbs = [lbfun(sig_lb(lst, x0, yy, i0, i1, fd, b), b) for b in boxes]
        if all(ok(k, l) for k, l in enumerate(lbs)):
            return (len(boxes) * (i1 - i0) + costw * len(far), x0, yy, i0, i1, lbs)
    return None

def mkbox(ya40, yb40):
    """ray box for the y-range [ya40, yb40] (units 2^-40, y = 3u): x range of the tube with W = 2^-30."""
    W = F(1, 2 ** 30)
    xlo = math.floor((-R0 - F(yb40, 3 * Z) - W) * Z); xhi = math.ceil((-R0 - F(ya40, 3 * Z) + W) * Z)
    return (xlo, xhi, ya40, yb40)

# ---------- legacy cell decoding ----------
def slot(Pn, i): return ((Pn >> (64 * i)) % 2 ** 64) - 2 ** 62
def getP(fname, name):
    t = open(LEG + fname, encoding='utf-8').read()
    return int(re.search(r'def %s : Nat := (\d+)' % name, t).group(1))
def legacy_ray():
    cache = ROOT + 'outputs/claude-2026-10-16/FX-lean-wp/CERTH/legacy_ray.json'
    if os.path.exists(cache): return json.load(open(cache))
    cells = []
    for n in range(27):
        Pn = getP('RayM%d.lean' % n, 'RayM%dP' % n)
        for i in range(1024):
            j, c = i // 32, i % 32
            a = j * 132 + 4 + 4 * c
            cells.append([slot(Pn, a), slot(Pn, a + 1), slot(Pn, a + 2), slot(Pn, a + 3)])
    json.dump(cells, open(cache, 'w'))
    return cells
def legacy_seg():
    cache = ROOT + 'outputs/claude-2026-10-16/FX-lean-wp/CERTH/legacy_seg.json'
    if os.path.exists(cache): return json.load(open(cache))
    cells = []
    for name, nm in (('SegA.lean', 'SegAP'), ('SegB.lean', 'SegBP')):
        Pn = getP(name, nm)
        for j in range(44):
            for c in range(32):
                a = j * 100 + 4 + 3 * c
                cells.append([slot(Pn, a), slot(Pn, a + 1), slot(Pn, a + 2)])
    json.dump(cells, open(cache, 'w'))
    return cells
