"""Compare the Lean window-cell price (base3 of the best feasible run) with the Python UF cells (gain_lower_pieces)."""
import sys, json
sys.path.insert(0, 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/scripts/claude/bank/uf')
sys.path.insert(0, 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/lean-plan-2026-10-27/evidence/claude/H11/py')
sys.argv = ['x']
import plan as P, gen as G
import genbank as GB
import newprice as N
from fractions import Fraction as F
q, a, al, sc = GB.BANKS['thirds']
prev = json.load(open(GB.CP + sc)); left = F(prev['left']); right = F(prev['right'])
r = 4000
tot = {}
for ci in (0, 1):
    rec = prev['records'][ci]; cls = rec['prime_class']
    c = N.context(q, a, F(al)); ns = GB.patched_formula(); ns['PAIRS'].clear()
    res = ns['formula_band'](c, left, right, cls, limits=N.LIM)
    cells = res['cells']
    def pygain(th):
        for cell in cells:
            if F(cell['left']) <= th <= F(cell['right']):
                best = 0
                for pc in cell['gain_lower_pieces']:
                    if F(pc['left']) <= th <= F(pc['right']):
                        best = max(best, float(F(pc['line']['intercept']) + F(pc['line']['slope']) * th))
                return best
        return 0
    n = 0; s_l = 0; s_p = 0; worst = (0, None); cnt = 0
    th = 0.3005
    while th < 3.9:
        p0 = int(th * r)
        p = next(x for x in range(p0, p0 + 400) if P.isprime(x) and x % 6 == cls)
        S, key, meets = G.structure(r, p)
        m, N0, rho = S['m'], S['N0'], S['rho']
        cands = []
        for i, R in enumerate(S['runs']):
            if not meets[i]: continue
            J = P.sig(rho, *R['stype'])
            ok = all(P.sig(rho, *S['runs'][k]['stype']) != J for k in range(3) if k != i and meets[k])
            if ok: cands.append(P.base3_exact(m, r, p, R['start'], R['end']))
        nat = 2 * (r + m) - m
        lg = (nat - min(cands)) / r if cands else 0
        pg = pygain(F(p, r))
        s_l += lg; s_p += pg; n += 1
        if pg - lg > worst[0]: worst = (pg - lg, (p / r, lg, pg))
        th += 0.01
    print('class', cls, 'mean lean gain', s_l / n, 'mean python gain', s_p / n, 'worst gap', worst)
