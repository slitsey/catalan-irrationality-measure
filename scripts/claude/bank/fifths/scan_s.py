"""For every S piece of uf-meta2.json find the closed-price candidate (kappa, zeta, q=r//p) that stays within a few units
of the piece line over all sampled (r, p, u).  Writes s-cand.json."""
import sys, json
sys.path.insert(0, 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/scripts/claude/bank/fifths')
from closed import *
from fractions import Fraction as Q
R = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/scripts/claude/bank/fifths/'
d = json.load(open(R + 'uf-meta2.json'))
out = {}
for jk, c in d['classes'].items():
    kappa = Q(c['kappa']); j = int(kappa * 5)
    res = []
    for idx, pc in enumerate(c['pieces']):
        if pc['layer'] != 'S': continue
        a, b = Q(pc['left']), Q(pc['right']); A, B = float(Q(pc['line'][0])), float(Q(pc['line'][1]))
        ok = {(kk, zz): True for kk in (False, True) for zz in (False, True)}
        qs = set(); worst = {}
        for r in (2000000, 2000010, 3000002):
            m = border(r)
            n = 220
            step = max(1, int((b - a) * r) // n)
            for u in (1, 2, 3, 4):
                for p in range(int(a * r) + 1, int(b * r) + 1, step):
                    if (j * p + u) % 5: continue
                    k = (j * p + u) // 5
                    qs.add(r // p)
                    line = A * r + B * p
                    for kk in (False, True):
                        for zz in (False, True):
                            dv = candPrice(m, r, p, k, kk, zz) - line
                            worst[(kk, zz)] = max(worst.get((kk, zz), -1e18), dv)
        good = [kz for kz, w in worst.items() if w <= 6]
        res.append(dict(idx=idx, left=pc['left'], right=pc['right'], line=pc['line'], qs=sorted(qs), cand=good, worst={str(k): v for k, v in worst.items()}))
        print(jk, idx, pc['left'], pc['right'], sorted(qs), good, {str(k): round(v, 1) for k, v in worst.items() if v < 50})
    out[jk] = res
json.dump(out, open(R + 's-cand.json', 'w'), indent=1)
