# Exact integer mirror of the Lean SigmaHybS checks (HMacro.lean): hybrid single list (masses sum 9*2^29), rho = 1/4096, slope 5/2, r0 = 7/50.
# Data: leandata/final4_tight.json (analytic-headroom).  Everything here must agree with CatalanCore/Cert/SigmaHybS/*.lean.
import json, math, sys, os, bisect
sys.set_int_max_str_digits(0)
sys.path.insert(0, 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-shift/scripts/certgen-p6')
from fractions import Fraction as F
from tables import tup, tlo, alo, JM

ROOT = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/'
DATA = os.environ.get('HS_DATA', ROOT + 'outputs/Compatibility programme/shift-nonclean-2026-10-22/analytic-headroom/leandata/final4_tight.json')
OUTD = ROOT + 'work/catalan-shift/CatalanCore/Cert/SigmaHybS/'
RHOE = 56
RHO2 = 2 ** RHOE
Z = 2 ** 40
P = 2 ** 64
R0 = F(7, 50)
SL = F(5, 2)
PILO = F(314159265358979323846, 10 ** 20)
L2UP = F(6931471808, 10 ** 10)

_D = None
def data():
    global _D
    if _D is None:
        _D = json.load(open(DATA))
    return _D

def pts_sorted():
    p = [tuple(x) for x in data()['points']]
    assert p == sorted(p, key=lambda q: (q[0], q[1]))
    return p

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

def theta0(vlo):   # thetaQ
    j = min(math.floor(vlo * 256), JM)
    return F(alo[j], P) + (0 if j == JM else (vlo - F(j, 256)) / (1 + F(j + 1, 256) ** 2))
def thetaX(vlo):
    if vlo >= F(JM, 256):
        w = (vlo - F(1, 2)) / (1 + vlo / 2)
        return F(alo[128], P) + theta0(w)
    return theta0(vlo)

def rest_core(b, th):
    xlo, xhi, ylo, yhi = b
    L1 = F(logUpS(xlo * xlo + yhi * yhi), P)
    A = F(1, 2) * max(F(-xhi, Z) * L1, F(-xlo, Z) * L1)
    l = F(logLoS((Z - xhi) ** 2 + ylo * ylo), P)
    B = -F(1, 2) * min(F(Z - xhi, Z) * l, F(Z - xlo, Z) * l)
    den = xlo * xlo + yhi * yhi - xlo * Z
    t = th(F(ylo * Z, den))
    C = -min(F(ylo, Z) * t, F(yhi, Z) * t)
    return 1 + A + B + C
def ubUp(xlo, xhi, ylo, yhi):          # legacy UbUp (thetaQ)
    assert xhi < 0 and xlo <= xhi and ylo >= 0
    return rest_core((xlo, xhi, ylo, yhi), theta0)
def uexUp(xlo, xhi, ylo, yhi):
    return F(1, 8) * ubUp(4 * xlo - 2 ** 42, 4 * xhi - 2 ** 42, 4 * ylo, 4 * yhi) + L2UP / 4
def rayRest(b):    # boxLBH(Ls, b) = Ls - rayRest(b)
    xlo, xhi, ylo, yhi = b
    assert xhi < 0 and xlo <= xhi and ylo >= 0
    return rest_core(b, thetaX) - F(999, 1000) * PILO * F(ylo, Z) + uexUp(*b)

# ---- real axis
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
def sideReal(xlo, xhi):
    if not xlo <= xhi: return False
    ok = (xhi <= 0 and -Z <= xlo) or (0 <= xlo and xhi <= Z)
    if not ok: return False
    if xhi <= 0: return True
    return 0 <= xlo and xlo <= xhi and xhi <= Z and (xhi != Z or 3 * 2 ** 38 <= xlo)
def realRest(c):   # realLBH = sig_lb - realRest
    xlo, xhi = c[0], c[1]
    assert sideReal(xlo, xhi)
    if xhi <= 0: return ut_A(xlo, xhi) + uexUp(xlo, xhi, 0, 0)
    return ut_B(xlo, xhi) + uexAxisUp(xlo, xhi)

# ---- Taylor machinery
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
def sig_lb(pts, x0, y0, i0, i1, fd, box):
    xlo, xhi, ylo, yhi = box
    L, Ax, Ex, Ay, Ey, H = fd
    ulo, uhi, vlo, vhi = xlo - x0, xhi - x0, ylo - y0, yhi - y0
    lin = 2 * (maxprod(Ax - Ex, Ax + Ex, ulo, uhi) + maxprod(Ay - Ey, Ay + Ey, vlo, vhi))
    quad = H * (max(ulo * ulo, uhi * uhi) + max(vlo * vlo, vhi * vhi))
    return F(-near_sum(box, pts[i0:i1]), 2 ** 97) - F(L, 2 ** 97) - F(lin + quad, 2 ** 133)

DS = [0.004, 0.008, 0.016, 0.03, 0.06, 0.12, 0.25, 0.5, 1, 10]
def window(KX, x0, Dd):
    return bisect.bisect_left(KX, x0 - int(Dd * Z)), bisect.bisect_right(KX, x0 + int(Dd * Z))

def macro_choose(pts, KX, boxes, rests, thr, costw=2.0, DSL=DS, y0=None, centre=None):
    """boxes: tuples (xlo,xhi,ylo,yhi); rests: rest(b) values; thr(k)->required lower bound for lb_k = sig_lb - rest_k.
    Returns (cost,x0,y0,i0,i1,lbs) or None."""
    xs = min(b[0] for b in boxes); xe = max(b[1] for b in boxes); ys = min(b[2] for b in boxes); ye = max(b[3] for b in boxes)
    x0 = (xs + xe) // 2; yy = (ys + ye) // 2 if y0 is None else y0
    for Dd in DSL:
        i0, i1 = window(KX, x0, Dd)
        far = pts[:i0] + pts[i1:]
        fd = far_data(x0, yy, far)
        lbs = [sig_lb(pts, x0, yy, i0, i1, fd, b) - r for b, r in zip(boxes, rests)]
        if all(l >= thr(k) for k, l in enumerate(lbs)):
            return (len(boxes) * (i1 - i0) + costw * len(far), x0, yy, i0, i1, lbs)
    return None

BIAS = 2 ** 62
def pack(slots):
    assert all(abs(v) < BIAS for v in slots)
    return sum((v + BIAS) << (64 * k) for k, v in enumerate(slots))
def slot(Pn, i): return ((Pn >> (64 * i)) % 2 ** 64) - 2 ** 62
