import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import json, traceback
sys.dont_write_bytecode = True
from fractions import Fraction as F
import genpk, profile13 as P
D = os.path.dirname(os.path.abspath(__file__))
sel = json.load(open(D + '/sel532.json'))
byk = {}
for g, k, a, b, c0, c1 in sel: byk.setdefault(k, []).append((F(a), F(b), F(c0), F(c1)))
OUT = 'CatalanMeasure/GenD/Uniform/Bank532/Pk/'
res = {}
final = {}
only = sys.argv[1:]
import spec as SP
EPS = [F(0), F(1,2000), F(1,500), F(1,200)]
def fit(k, ws):
    sp = SP.spec(k); best = None
    for N0b in (None, 60, 200, 600):
        for el in EPS:
            for er in EPS:
                w2 = [(a + el, b - er, c0, c1) for a, b, c0, c1 in ws]
                if any(a >= b for a, b, *_ in w2): continue
                N0 = max(20, 2 * max(w[0].denominator for w in w2)) if N0b is None else max(N0b, 2 * max(w[0].denominator for w in w2))
                ha = min(w[0] for w in w2); hb = max(w[1] for w in w2)
                if SP.weights_ok(sp, ha, hb, N0) or SP.check_domain(sp, ha, hb, N0): continue
                loss = sum(P.line_area(c0, c1, a, b) for a, b, c0, c1 in ws) - sum(P.line_area(c0, c1, a, b) for a, b, c0, c1 in w2)
                if best is None or loss < best[0]: best = (loss, N0, w2)
        if best: return best
    return None

for k, ws in byk.items():
    if k.startswith('D58-L0146') or (only and k not in only): continue
    nm = k.replace('D58-', '').replace('|', '_')
    ft = fit(k, ws)
    if ft is None: print('NOFIT', k, flush=True); continue
    loss, N0, ws = ft; final[k] = [[str(x) for x in w] for w in ws]
    try:
        info = genpk.gen(k, OUT + nm + '.lean', N0, ws); res[k] = info; print('OK', k, 'N0', N0, 'loss', float(loss), info['n'], info['d'], info['bytes'], info['secs'], flush=True)
    except Exception as e:
        print('FAIL', k, repr(e)[:300], flush=True)
json.dump(res, open(D + '/genall.json', 'w'))
json.dump(final, open(D + '/final532.json', 'w'))
