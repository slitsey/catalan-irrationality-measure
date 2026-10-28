import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sys, json
sys.dont_write_bytecode = True
sys.path.insert(0, 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/scripts/claude/bank/g532')
from fractions import Fraction as F
import profile13 as P
PIECES = P.PROG + 'G-content-closed-form-2026-10-27/data/pieces.txt'
def pieces():
    out = []
    for l in open(PIECES, encoding='utf-8'):
        t = l.split()
        if len(t) >= 4 and t[0].startswith('D58-L'):
            a, b = P.num(t[1]), P.num(t[2])
            if t[3] == 'line': out.append((t[0], a, b, F(t[4]), F(t[5])))
            else: out.append((t[0], a, b, F(0), F(0)))
    return out
def ledger_overlap(W, a, b, c0, c1):
    """integral over (a,b) of max(0, full - ledger)"""
    # breakpoints
    pts = sorted({a, b} | {x for w in W for x in (w[0], w[1]) if a < x < b})
    tot = F(0)
    for u, v in zip(pts, pts[1:]):
        mid = (u + v) / 2
        led = F(0); lc = (F(0), F(0))
        for w in W:
            if w[0] < mid <= w[1]: lc = (w[2], w[3])
        d0, d1 = c0 - lc[0], c1 - lc[1]
        # d0+d1 x on (u,v): positive part integral (assume sign constant or handle crossing)
        fu, fv = d0 + d1 * u, d0 + d1 * v
        if fu >= 0 and fv >= 0: tot += P.line_area(d0, d1, u, v)
        elif fu <= 0 and fv <= 0: pass
        else:
            r = -d0 / d1
            tot += P.line_area(d0, d1, u, r) if fu > 0 else P.line_area(d0, d1, r, v)
    return tot
if __name__ == '__main__':
    W = P.load(); pcs = pieces()
    full = sum(P.line_area(c0, c1, a, b) for _, a, b, c0, c1 in pcs)
    print('full', float(full), 'ledger', float(sum(P.area(w) for w in W)))
    gaps = {}
    for lf, a, b, c0, c1 in pcs:
        g = ledger_overlap(W, a, b, c0, c1)
        if g: gaps.setdefault(lf, []).append((float(g), float(a), float(b), str(c0), str(c1)))
    tot = sum(sum(x[0] for x in v) for v in gaps.values()); print('total gap', tot, 'leaves', len(gaps))
    rows = sorted(((sum(x[0] for x in v), k) for k, v in gaps.items()), reverse=True)
    cum = 0
    for g, k in rows:
        cum += g; print(k, round(g, 5), round(cum, 5), [(round(x[1], 3), round(x[2], 3)) for x in gaps[k]])
    json.dump(gaps, open('C:/Users/seanl/AppData/Local/Temp/claude/gaps13.json', 'w')) if False else None
