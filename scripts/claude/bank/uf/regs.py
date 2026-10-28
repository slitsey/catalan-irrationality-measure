"""H13: Reg field lists of the thirds families (same texts as gen.fam_lean) + python evaluator."""
import sys, os, json, re
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import plan as P
N0X = "(r + 2 * ((3 * r + 9) / 20))"

def fields_of(F):
    """(lin, cmps): lin = [(name, lean text)], cmps = [(name, op, (t0,tv), (t0',tv'))]."""
    rho, jm, j1, br, meets = F['key']
    D = F['D']; w = F['w']; runs = D['runs']
    fields = [('hr', 'r % 2 = 0'), ('hp3', f'p % 3 = {rho}'), ('hlo', '3 * r < 10 * p'), ('hhi', '10 * p ≤ 39 * r'),
              ('hp60', '60 ≤ p'), ('hM1', f'{jm - 1} * p < r'), ('hM2', f'r ≤ {jm} * p'),
              ('hP1', f'{j1 - 3} * p + 2 < 3 * r' if j1 >= 4 else '0 < r'), ('hP2', f'3 * r ≤ {j1} * p + 2')]
    if br is not None:
        fields += [('hb1', f'{br} * p + 2 ≤ 3 * r'), ('hb2', f'3 * r < {br + 1} * p + 2')]
    S1 = D['S1']
    fields.append(('hm0', f'r < {S1}' if meets[0] else f'{S1} ≤ r'))
    fields.append(('hf1', f"{D['ST1']} < {N0X}" if meets[1] else f"{N0X} ≤ {D['ST1']}"))
    fields.append(('hf2', f"{D['ST2']} < {N0X}" if meets[2] else f"{N0X} ≤ {D['ST2']}"))
    cmps = []
    for w2 in F['feas']:
        if w2 == w: continue
        cmps.append((f'hc{w2}', '<' if w2 < w else '≤', (runs[w]['start'], runs[w]['end']), (runs[w2]['start'], runs[w2]['end'])))
    return fields, cmps

def pyexpr(t):
    t = t.replace('≤', '<=')
    t = re.sub(r'(?<![<>=!])=(?!=)', '==', t)
    return t.replace('/', '//')

class Fam:
    def __init__(self, F):
        self.F = F
        lin, self.cmps = fields_of(F)
        self.lin = [(n, t, compile(pyexpr(t), n, 'eval')) for n, t in lin]
        self.ce = [(n, o, compile(pyexpr(a), n, 'eval'), compile(pyexpr(b), n, 'eval'),
                    compile(pyexpr(c), n, 'eval'), compile(pyexpr(d), n, 'eval')) for n, o, (a, b), (c, d) in self.cmps]
    def holds(self, r, p):
        env = dict(r=r, p=p)
        for n, t, c in self.lin:
            if not eval(c, {}, env): return False
        m = (3 * r + 9) // 20
        for n, o, a, b, c, d in self.ce:
            x = P.base3_exact(m, r, p, eval(a, {}, env), eval(b, {}, env))
            y = P.base3_exact(m, r, p, eval(c, {}, env), eval(d, {}, env))
            if not ((x < y) if o == '<' else (x <= y)): return False
        return True

def load(path):
    fams = [f for f in json.load(open(path)) if not f.get('infeasible')]
    for f in fams: f['key'][4] = tuple(f['key'][4])
    return fams


def _price(self, r, p):
    D = self.F['D']; w = self.F['w']; run = D['runs'][w]
    env = dict(r=r, p=p)
    t0 = eval(compile(pyexpr(run['start']), 't0', 'eval'), {}, env)
    tv = eval(compile(pyexpr(run['end']), 'tv', 'eval'), {}, env)
    return P.base3_exact((3 * r + 9) // 20, r, p, t0, tv)


Fam.price = _price
