# Exact integer mirror of the Lean SigmaP6 ray/segment/line checks (port of paper-lambda/scripts/lean-cert/mirror*.py).
# Config (module constants): sigma file, r0 = 1/10, rho^2 * 2^80 = 2^RHOE, arctan extension past j = JM via arctan(1/2) shift.
import json, math, sys, os, bisect
sys.set_int_max_str_digits(0)
from fractions import Fraction as F
from tables import *
SIGMA = os.environ.get('P6_SIGMA', 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/claude-2026-10-16/FK-P6-decay/sigma/sig_p6_r010_K700w.json')
R0 = F(1, 10)
RHOE = 58            # rho = 1/2048: rho^2 * 2^80 = 2^58
RHO2 = 2 ** RHOE
Z = 2 ** 40; P = 2 ** 64
sig = json.load(open(SIGMA))
assert sig['rho'] == '1/2048' and sig['pos_den'] == 2 ** 24 and sig['mass_den'] == 2 ** 32
pts = []
for X, Y, n in sig['points']:
    pts.append((X << 16, Y << 16, n))
    if Y > 0: pts.append((X << 16, -(Y << 16), n))
spts = sorted(pts, key=lambda p: (p[0], p[1]))
assert sum(p[2] for p in spts) == 2 ** 32 and len(set(spts)) == len(spts)
KX = [p[0] for p in spts]
K = len(spts)
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
PILO = F(314159265358979323846, 10 ** 20)
def theta0(vlo):
    j = min(math.floor(vlo * 256), JM)
    return F(alo[j], P) + (0 if j == JM else (vlo - F(j, 256)) / (1 + F(j + 1, 256) ** 2))
def theta(vlo):   # extension: v >= JM/256 -> arctan v = arctan(1/2) + arctan((v-1/2)/(1+v/2))
    if vlo >= F(JM, 256):
        w = (vlo - F(1, 2)) / (1 + vlo / 2)
        return F(alo[128], P) + theta0(w)
    return theta0(vlo)
def ray_rest(b):   # box_lb = Ls - rest
    xlo, xhi, ylo, yhi = b
    L1 = F(logUpS(xlo * xlo + yhi * yhi), P)
    A = F(1, 2) * max(F(-xhi, Z) * L1, F(-xlo, Z) * L1)
    wl = (Z - xhi) ** 2 + ylo * ylo
    l = F(logLoS(wl), P); c1 = F(Z - xhi, Z); c2 = F(Z - xlo, Z)
    B = -F(1, 2) * min(c1 * l, c2 * l)
    den = xlo * xlo + yhi * yhi - xlo * Z
    th = theta(F(ylo * Z, den))
    C = -min(F(ylo, Z) * th, F(yhi, Z) * th)
    return 1 + A + B + C - F(999, 1000) * PILO * F(ylo, Z)
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
def sig_lb(x0, y0, i0, i1, fd, box):
    xlo, xhi, ylo, yhi = box
    L, Ax, Ex, Ay, Ey, H = fd
    ulo, uhi, vlo, vhi = xlo - x0, xhi - x0, ylo - y0, yhi - y0
    lin = 2 * (maxprod(Ax - Ex, Ax + Ex, ulo, uhi) + maxprod(Ay - Ey, Ay + Ey, vlo, vhi))
    quad = H * (max(ulo * ulo, uhi * uhi) + max(vlo * vlo, vhi * vhi))
    return F(-near_sum(box, spts[i0:i1]), 2 ** 97) - F(L, 2 ** 97) - F(lin + quad, 2 ** 133)
DS = [0.004, 0.008, 0.016, 0.03, 0.06, 0.12, 0.25, 0.5, 1, 10]
def window(x0, Dd):
    i0 = bisect.bisect_left(KX, x0 - int(Dd * Z)); i1 = bisect.bisect_right(KX, x0 + int(Dd * Z))
    return i0, i1
def mkbox(ua, ub):
    ua40 = math.floor(ua * Z); ub40 = math.ceil(ub * Z)
    W = F(1, 2 ** 30)
    xlo = math.floor((-R0 - F(ub40, Z) - W) * Z); xhi = math.ceil((-R0 - F(ua40, Z) + W) * Z)
    return (xlo, xhi, 3 * ua40, 3 * ub40)
def macro_choose(boxes, rest, thr, costw=2.0, DSL=DS):
    xs = min(b[0] for b in boxes); xe = max(b[1] for b in boxes); ys = min(b[2] for b in boxes); ye = max(b[3] for b in boxes)
    x0 = (xs + xe) // 2; y0 = (ys + ye) // 2
    rs = [rest(b) for b in boxes]
    for Dd in DSL:
        i0, i1 = window(x0, Dd)
        far = spts[:i0] + spts[i1:]
        fd = far_data(x0, y0, far)
        if all(sig_lb(x0, y0, i0, i1, fd, b) - r >= thr for b, r in zip(boxes, rs)):
            return (len(boxes) * (i1 - i0) + costw * len(far), x0, y0, i0, i1)
    return None
