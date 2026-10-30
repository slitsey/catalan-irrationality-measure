"""Fifths UF strict profile (lane B, B5c): min(T, S, LP, M3D) [+R optional], reproduces replay-fifths UF rational.
Usage: profile_uf.py [withR]   Writes uf-meta.json (pieces with layer tags; S pieces carry the S line)."""
from pathlib import Path
from fractions import Fraction as Q
import json, sys, math
sys.dont_write_bytecode = True
R = Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform')
P = R.parents[1] / 'outputs/Compatibility programme'
sys.path.insert(0, str(P / 'hybrid-alpha-2026-10-27'))
import _paths
sys.path.insert(0, str(P / 'q4-mechanisms-uniform-2026-10-27'))
import newprice as N, m3
Line = N.Line
withR = len(sys.argv) > 1 and sys.argv[1] == 'withR'
al = Q(1, 9); left = 2 * al; hi3 = 1 + 4 * al; right = Q(55, 9)
D = json.loads((P / 'bank-specs-2026-10-28/rank-fifths.json').read_text())
prev = json.load(open(P / 'scope-screen-2026-10-27/s-q5-a1-alpha1_9-lo2_9.json'))
c = N.context(5, 1, al)
assert c.binding == prev['context_binding']
res = {}
for case in D['cases']:
    ka = Q(case['pole_cut']); t = case['prime_class']
    rank = [(Q(v['left']), Q(v['right']), Line(Q(v['line'][0]), Q(v['line'][1]))) for cc in case['cells'] for v in cc['price_pieces']]
    S = N.pieces_of(N.formula_band(c, left, right, t, limits=N.LIM)['cells'], 'price_upper_pieces')
    cuts = {al, left, right, hi3} | {x for x in N.breakpoints(al, ka) if left < x < right} | {x for x in N.g_kinks(al, ka) if left < x < right}
    cuts |= {x for u, v, f in rank for x in (u, v)} | {x for u, v, f in S for x in (u, v)}
    fine = set(cuts)
    for u, v in zip(sorted(cuts), sorted(cuts)[1:]):
        if u < hi3: fine |= m3.kinks(al, ka, u, min(v, hi3))
    fine = sorted(x for x in fine if al <= x <= right)
    pieces = []
    for u, v in zip(fine, fine[1:]):
        mid = (u + v) / 2
        T = Line(2 + 3 * al, Q(-1)) if mid < left else N.trop_line(u, v, al, ka)
        ls = [('T', T)]
        if mid >= left:
            if withR: ls.append(('R', next(f for a, b, f in rank if a < mid < b)))
            ls.append(('S', next(f for a, b, f in S if a < mid < b)))
            g = N.g_line(mid, al, ka)
            if 1 < mid and ka * mid < 1 and (1 + ka) * mid < 1 + 2 * al: g = Line(Q(0), Q(0))
            ls.append(('LP', Line(T.intercept - g.intercept, T.slope - g.slope)))
        if mid < hi3: ls.extend(('M3D', f) for f in m3.P3_lines(al, ka, u, v))
        sub = {u, v}
        for _, f in ls:
            for _, g in ls:
                if f.slope != g.slope:
                    x = (g.intercept - f.intercept) / (f.slope - g.slope)
                    if u < x < v: sub.add(x)
        for a, b in zip(sorted(sub), sorted(sub)[1:]):
            md = (a + b) / 2
            tag, f = min(ls, key=lambda tf: tf[1](md))
            rec = dict(left=str(a), right=str(b), line=[str(f.intercept), str(f.slope)], layer=tag)
            if pieces and pieces[-1]['line'] == rec['line'] and pieces[-1]['right'] == rec['left'] and pieces[-1]['layer'] == tag:
                pieces[-1]['right'] = rec['right']
            else: pieces.append(rec)
    mass = sum((Q(v['line'][0]) * (Q(v['right']) - Q(v['left'])) + Q(v['line'][1]) * (Q(v['right']) ** 2 - Q(v['left']) ** 2) / 2 for v in pieces), Q(0))
    res[t] = dict(prime_class=t, kappa=str(ka), pieces=pieces, mass=str(mass))
prefix = 4 * al + 2 * al ** 2 - ((2 + 3 * al) * al - Q(3, 2) * al ** 2)
A_ = prefix + sum((Q(c_['mass']) for c_ in res.values()), Q(0)) / 4
expected = Q(json.loads((P / 'bank-specs-2026-10-28/replay-fifths.json').read_text())['UF']['rational'])
print('withR', withR, 'Lambda==replay UF:', A_ == expected, float(A_), float(expected))
from collections import Counter
for t, c_ in res.items(): print(t, dict(Counter(p['layer'] for p in c_['pieces'])))
(R / ('scripts/claude/bank/fifths/uf-meta%s.json' % ('R' if withR else ''))).write_text(json.dumps(dict(lam=str(A_), classes=res), indent=1))
