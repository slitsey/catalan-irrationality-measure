import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/scripts/claude/bank/g532')
from fractions import Fraction as F
import packetinfo as PI, gaps13 as G, profile13 as P
W = P.load(); pcs = G.pieces()
allinfo = {}
def inf(k):
    if k not in allinfo: allinfo[k] = PI.info(k)
    return allinfo[k]
rows = []
for lf, a, b, c0, c1 in pcs:
    if not (c0 or c1): continue
    g = G.ledger_overlap(W, a, b, c0, c1)
    if not g: continue
    m = []
    for k, p in PI.packets().items():
        i = inf(k)
        v = i['val']
        if v[1] == c0 and v[2] == c1 and v[0] >= -2:
            lo, hi = F(p['interval'][0]), F(p['interval'][1])
            if lo <= a and b <= hi: m.append((k, i['n'], i['d'], str(v[0])))
    rows.append((float(g), lf, a, b, c0, c1, m))
rows.sort(reverse=True)
for g, lf, a, b, c0, c1, m in rows[:60]:
    print(round(g, 5), lf, float(a), float(b), '%s+%sx' % (c0, c1), m)
print('---- x>3 greedy')
cum = 0; sel = []
for g, lf, a, b, c0, c1, m in rows:
    if a < 3 or not m: continue
    cum += g; sel.append((lf, float(a), m[0][0], round(g, 5), round(cum, 5)))
for s in sel[:40]: print(s)
print('---- overlaps')
selp = [(lf, a, b, c0, c1, m[0][0]) for g, lf, a, b, c0, c1, m in rows if a >= 3 and m][:34]
for lf, a, b, c0, c1, k in selp:
    ov = [(float(w[0]), float(w[1]), str(w[2]), str(w[3])) for w in W if w[0] < b and w[1] > a]
    print(lf, float(a), float(b), k, 'OLD:', ov)
