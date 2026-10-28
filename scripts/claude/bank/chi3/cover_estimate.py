"""STEP 0 (B3): cover + cost estimate for the chi3 bank (read only, no Lean emitted).
Maps the receipt cover (ray / line / seg cells, rule endpoint|logjet8) to Lean cell kinds:
  ray   endpoint -> mixOk (D6d) ; logjet8 -> cellOk'(jetM) ; cells straddling a polygon vertex are split
  line  endpoint -> mixOk, logjet8 -> cellOk' ; seg(cap) -> cellOk' (capLb cell, same rule as a line cell)
Cost: per cell 0.45 s * (#segments) + 8 s  (D6b), order 6 gives about -20%.
"""
import json, sys, os
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import gen_bank
d = gen_bank.derive('Chi3')
cov = d['covers']; poly = d['poly']['vertices']
nseg = len(d['segs'])
rows, cols = d['geom']['rows'], d['geom']['cols']
nnode = len(rows) + len(cols)       # node pieces RP ++ CP
N = nseg + nnode
ys = sorted(set(v[1] for v in poly))
print('trial pieces', nseg, 'node pieces', nnode, 'segments N', N)
print('vertex y', [float(y) for y in ys])
tot = {}
def cnt(key, name):
    cs = cov[key]; e = sum(1 for c in cs if c['rule'] == 0); j = len(cs) - e
    extra = 0
    if key == 'ray':
        for c in cs:
            extra += sum(1 for y in ys if c['a'] < y < c['b'])
    print(f"{key}: {len(cs)} receipt cells, endpoint={e}, logjet8={j}, vertex splits={extra}")
    tot[key] = (e, j, extra)
for k in ('ray', 'line', 'seg'): cnt(k, k)
cells = sum(e + j + x for e, j, x in tot.values())
per8 = 0.45 * N + 8
per6 = 0.8 * per8
print(f"cells total {cells}; per-cell kernel {per8:.1f}s (order 8) {per6:.1f}s (order 6)")
for lbl, per in (('order 8', per8), ('order 6 everywhere', per6)):
    print(f"kernel CPU {lbl}: {cells*per/3600:.2f} h")
# far ray cells (rough: cells with a > 1/2 of the last vertex height use cheaper far rule: not credited)
src = sum(1 for _ in open(gen_bank.OUTBASE + '/Chi3/CellInfo.lean', encoding='utf8'))
print('existing sl-format data bytes', sum(os.path.getsize(os.path.join(gen_bank.OUTBASE,'Chi3',f)) for f in os.listdir(os.path.join(gen_bank.OUTBASE,'Chi3'))))
# widest ratio cells next to vertex singularities (need merging/subdivision)
print('ray cells (a,b) first 8', [(str(c['a']), str(c['b']), c['rule']) for c in cov['ray'][:8]])
print('cell-source estimate: ~5 KB/cell exact C => %.1f MB' % (cells*5/1000))
