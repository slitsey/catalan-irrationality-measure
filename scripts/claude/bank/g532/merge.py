"""G10: envelope merge of wins13 with new packet piece windows; exact checks.  Output: plan json."""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import json
sys.dont_write_bytecode = True
from fractions import Fraction as F
import profile13 as P, gaps13 as G, packetinfo as PI
def selection(nmax=34):
    W = P.load(); pcs = G.pieces(); out = []
    INF = {k: PI.info(k) for k in PI.packets()}
    for lf, a, b, c0, c1 in pcs:
        if not (c0 or c1) or a < 3: continue
        g = G.ledger_overlap(W, a, b, c0, c1)
        if not g: continue
        for k, p in PI.packets().items():
            i = INF[k]; v = i['val']
            if v[1] == c0 and v[2] == c1 and v[0] >= -2 and F(p['interval'][0]) <= a and b <= F(p['interval'][1]):
                out.append((float(g), k, a, b, c0, c1)); break
    out.sort(reverse=True)
    sel = out[:nmax]
    # L0146: Lean pilot window only to 152/25
    sel = [(g, k, a, (F(152, 25) if k.startswith('D58-L0146') else b), c0, c1) for g, k, a, b, c0, c1 in sel]
    return sel
def envelope(old, new):
    """old: list of (a,b,c0,c1,tag); new likewise.  returns list of (a,b,c0,c1,tag) sorted, max envelope."""
    allw = old + new
    pts = sorted({x for w in allw for x in (w[0], w[1])})
    pieces = []
    def val(w, x): return w[2] + w[3] * x
    for u, v in zip(pts, pts[1:]):
        cands = [w for w in allw if w[0] <= u and v <= w[1]]
        if not cands: continue
        # split at crossings
        xs = {u, v}
        for i, w1 in enumerate(cands):
            for w2 in cands[i + 1:]:
                if w1[3] != w2[3]:
                    r = (w2[2] - w1[2]) / (w1[3] - w2[3])
                    if u < r < v: xs.add(r)
        xs = sorted(xs)
        for s, t in zip(xs, xs[1:]):
            m = (s + t) / 2
            best = max(cands, key=lambda w: val(w, m))
            pieces.append((s, t, best[2], best[3], best[4]))
    # merge adjacent equal tag/line
    out = []
    for w in pieces:
        if out and out[-1][1] == w[0] and out[-1][2:] == w[2:]: out[-1] = (out[-1][0], w[1]) + w[2:]
        else: out.append(w)
    return out
def area(w): return P.line_area(w[2], w[3], w[0], w[1])
if __name__ == '__main__':
    sel = selection(int(sys.argv[1]) if len(sys.argv) > 1 else 34)
    W = P.load(); W.sort()
    old = [(a, b, c0, c1, ('old', i)) for i, (a, b, c0, c1) in enumerate(W)]
    new = [(a, b, c0, c1, ('new', k)) for g, k, a, b, c0, c1 in sel]
    E = envelope(old, new)
    for x, y in zip(E, E[1:]): assert x[1] <= y[0]
    ga = sum(area(w) for w in E); g13 = sum(area(w) for w in old)
    gap = sum(F(g) for g, *_ in sel)
    print('windows', len(E), 'gain13', float(g13), 'envelope gain', float(ga), 'increase', float(ga - g13), 'sum of float gaps', float(gap))
    print('need 532', 22.05325 - float(g13), '533', 22.00225 - float(g13), '534', 21.94225 - float(g13))
    print('gain532 >= 22.05325:', ga >= F(2205325, 100000), ' margin', float(ga - F(2205325, 100000)))
    json.dump([[str(x) for x in w[:4]] + [list(w[4])] for w in E], open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'plan532.json'), 'w'))
    json.dump([[g, k, str(a), str(b), str(c0), str(c1)] for g, k, a, b, c0, c1 in sel], open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'sel532.json'), 'w'))
    ntr = sum(1 for w in E if w[4][0] == 'old'); print('old kept/trimmed', ntr, 'new', len(E) - ntr)
