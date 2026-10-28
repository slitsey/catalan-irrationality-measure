"""B3c generator: M3D windows for the chi3 hybrid (alpha = 1/4) on theta in [1/4, 1/2].
Lower envelope of the old tropical line 11/4 - theta and the M3 witness lines (from cut lines), exact rationals.
Output: json with, per class, a tiling of [1/4,1/2] by pieces (source old | m3 with witness formulas)."""
import sys, json, math
from fractions import Fraction as F
AL = F(1, 4)
KAP = {1: [F(1, 3), F(1, 2)], 5: [F(2, 3), F(1, 2)]}
W = {1: [(F(1, 4), F(1, 2))], 5: [(F(1, 4), F(1, 2))]}

class Line:
    def __init__(s, i, sl): s.i = F(i); s.s = F(sl)
    def __call__(s, x): return s.i + s.s * x
    def key(s): return (s.i, s.s)

def cutlines(kas, lo, hi):
    xs = set(); nmax = int((1 + 2 * AL) / lo) + 2
    for n in range(0, nmax + 1):
        for x in [F(n)] + [n + k for k in kas]:
            if x > 0: xs.add(x)
    return [('cut0', Line(0, x)) for x in sorted(xs)] + [('cutr', Line(1, j)) for j in range(0, 3)]

LO = [('lo_r', Line(1, 0)), ('lo_p', Line(1 + 2 * AL, -1))]
HI = [('hi_m', Line(1 + 2 * AL, 0)), ('hi_p', Line(1, 1))]

def candidates(kas, u, v):
    m = (u + v) / 2
    cuts = cutlines(kas, u, v)
    wl = max(LO, key=lambda t: t[1](m)); wh = min(HI, key=lambda t: t[1](m))
    inner = sorted([c for c in cuts if wl[1](m) < c[1](m) < wh[1](m)], key=lambda c: c[1](m))
    pts = [wl] + inner + [wh]
    out = []
    for A, B in zip(pts, pts[1:]):
        if B[1](m) > A[1](m):
            ln = Line(F(5, 2) - (B[1].i - A[1].i), -(B[1].s - A[1].s))
            out.append((ln, A, B))
    return out

def kinks(kas, lo, hi):
    L = [c[1] for c in cutlines(kas, lo, hi)] + [x[1] for x in LO + HI]
    K = set()
    for a in range(len(L)):
        for b in range(a):
            f, g = L[a], L[b]
            if f.s != g.s:
                x = (g.i - f.i) / (f.s - g.s)
                if lo < x < hi: K.add(x)
    return K

def envelope(cands, u, v):
    """cands: list of (Line, tag). Return list of (s,t,Line,tag) pieces of the lower envelope on [u,v]."""
    xs = {u, v}
    for a in range(len(cands)):
        for b in range(a):
            f, g = cands[a][0], cands[b][0]
            if f.s != g.s:
                x = (g.i - f.i) / (f.s - g.s)
                if u < x < v: xs.add(x)
    xs = sorted(xs); res = []
    for s, t in zip(xs, xs[1:]):
        m = (s + t) / 2
        best = min(cands, key=lambda c: (c[0](m), 0 if c[1] == 'old' else 1))
        res.append((s, t, best[0], best[1]))
    return res

def pieces_for_class(cls):
    kas = KAP[cls]
    left, right = F(1, 4), F(1, 2)
    old = Line(F(11, 4), -1)
    # fine breakpoints: kinks of cut lines + crossings with old line
    fine = {left, right} | kinks(kas, left, right)
    for _, ln in cutlines(kas, left, right):
        pass
    fine = sorted(x for x in fine if left <= x <= right)
    allp = []
    for u, v in zip(fine, fine[1:]):
        cands = [(old, 'old')] + [(ln, ('m3', A[0], A[1].key(), B[0], B[1].key())) for ln, A, B in candidates(kas, u, v)]
        allp += envelope(cands, u, v)
    # merge adjacent with same tag
    merged = []
    for s, t, ln, tag in allp:
        if merged and merged[-1][3] == tag and merged[-1][2].key() == ln.key():
            merged[-1] = (merged[-1][0], t, ln, tag)
        else:
            merged.append((s, t, ln, tag))
    return merged

if __name__ == '__main__':
    tot = {}
    for cls in (1, 5):
        ps = pieces_for_class(cls)
        sav = F(0)
        for s, t, ln, tag in ps:
            if tag != 'old':
                oldv = (F(11, 4) * (t - s) - (t * t - s * s) / 2)
                newv = ln.i * (t - s) + ln.s * (t * t - s * s) / 2
                sav += oldv - newv
        print('class', cls, 'pieces', len(ps), 'm3 pieces', sum(1 for p in ps if p[3] != 'old'), 'saving', float(sav))
        for s, t, ln, tag in ps: print('  ', s, t, ln.i, ln.s, tag)
        tot[cls] = sav
    print('avg saving', float((tot[1] + tot[5]) / 2))
