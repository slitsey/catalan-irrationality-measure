"""Certificates for the existing Lean thirds template (Bank/ThirdsContent/Tmpl/*.lean) under the Lean checker
`BankShared.Check` (mirror.py), and the Lean regression data file (Check/Test.lean data part).

Constants as in C1's checker.py run on the Lean template: q = 3, alpha = 3/20, M = 6, members {1, 2}, depth 2,
c_Fr <= 25, P_bad = 5, alpha0 = 23/10, tau = 4, t1 = 3/1000 (prefix lemma thirds_pre_gle: t0 = 3/1000,
alpha0b = 23/10).  Usage: python -I gen_thirds_check.py [--emit]"""
import sys, re, json, math
from fractions import Fraction as F
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import mirror as X
WORK = HERE.parents[3]
TMPL = WORK / 'CatalanCore/Uniform/Bank/ThirdsContent/Tmpl'

def parse(name):
    txt = (TMPL / f'{name}.lean').read_text(encoding='utf-8')
    out = []
    for m in re.finditer(r'mkPiece (\d+) (\d+) (\d+) (\d+) \(?(-?\d+)\)? \(?(-?\d+)\)? (\d+) (\d+)', txt):
        out.append(tuple(map(int, m.groups())))
    return out

PRE = ['prefTmpl0', 'prefTmpl1', 'prefTmpl2']
PROF = {1: ['profTmpl1_0', 'profTmpl1_1'], 2: ['profTmpl2_0', 'profTmpl2_1']}

def qpiece(raw):
    sn, sd, tn, td, A, B, E, D = raw
    return (F(sn, sd), F(tn, td), F(A, D), F(B, D), F(E, D))

WINDOWS = [(n0, n1) for n0 in range(0, 12) for n1 in range(0, 12)]

def catalogue(wins):
    names = [n for n, _ in X.BASE] + [f'W{n0}_{n1}' for n0, n1 in wins]
    cat = [b for _, b in X.BASE] + [X.window(n0, n1) for n0, n1 in wins]
    return names, cat

def strip_line(tau, al, ka, e, left, W):
    """largest one-sided interval (e, e+w] / (e-w, e] (w <= W) on which `aff` succeeds."""
    if left:
        v = e + W
        while X.aff(tau, al, ka, e, v) is None:
            v = X.split_point(tau, al, ka, e, v)
        return v - e
    u = e - W
    while X.aff(tau, al, ka, u, e) is None:
        u = X.split_point(tau, al, ka, u, e)
    return e - u

def search(P, cat, names, q, al, ka, depth, cF, Pbad, only=None):
    s, t, a, b, Cc = P
    opts = []
    for bi, (tau, conds, deb) in enumerate(cat):
        if only is not None and bi not in only:
            continue
        ok = True
        needL = needR = False
        for c in conds:
            l = X.ell(c, al, ka)
            ls, lt = X.lv(l, s), X.lv(l, t)
            if ls < 0 or lt < 0 or ((ls == 0 or lt == 0) and l[1] == 0):
                ok = False; break
            if ls == 0 and not X.exactL(c, q): needL = True
            if lt == 0 and not X.exactR(c, q): needR = True
        if not ok:
            continue
        cuts = X.subdivide(tau, al, ka, s, t)
        pts = [s] + cuts + [t]
        good = True
        for u, v in zip(pts, pts[1:]):
            ln = X.aff(tau, al, ka, u, v)
            if X.lv(ln, u) > a + b * u or X.lv(ln, v) > a + b * v:
                good = False; break
        if not good:
            continue
        strips = []
        for left, e, want in ((True, s, needL), (False, t, needR)):
            if not want: continue
            best = None
            for yi, (ty, cy, dy) in enumerate(cat):
                if not all(X.lv(X.ell(c, al, ka), e) > 0 for c in cy): continue
                W = (t - s) if left else min(t - s, e / 2)
                w = strip_line(ty, al, ka, e, left, W)
                ln = X.aff(ty, al, ka, e, e + w) if left else X.aff(ty, al, ka, e - w, e)
                val = X.lv(ln, e)
                if val <= a + b * e and (best is None or val < best[0]):
                    best = (val, yi, w)
            if best is None:
                good = False; break
            strips.append((left, best[1], best[2]))
        if not good:
            continue
        cert = (bi, cuts, strips)
        res = X.piece_ok(P, cert, cat, q, al, ka, depth, cF, Pbad)
        if res[0]:
            opts.append(((len(strips), 0 if names[bi].startswith('T') else 1, bi), cert, res))
    if not opts:
        return None
    opts.sort(key=lambda z: z[0])
    return opts[0]

def build(wins=WINDOWS):
    names, cat = catalogue(wins)
    q, al = 3, F(3, 20)
    pre = sum((parse(n) for n in PRE), [])
    D = dict(q=3, M=6, al=al, members=[1, 2], depth=2, cF=25, Pbad=5, alpha0=F(23, 10), tau=F(4),
             alpha0b=F(23, 10), t0=F(3, 1000), cat=cat, iD6=5, tmpls={})
    used = {}
    stats = {}
    for j in (1, 2):
        raws = pre + sum((parse(n) for n in PROF[j]), [])
        ka = F(j, q)
        pcs = []
        for raw in raws:
            P = qpiece(raw)
            r = search(P, cat, names, q, al, ka, D['depth'], D['cF'], D['Pbad'])
            if r is None:
                print('NO CERT', j, P[:4]); pcs.append((P, (0, [], []))); continue
            _, cert, res = r
            used[names[cert[0]]] = used.get(names[cert[0]], 0) + 1
            for _, yi, _ in cert[2]:
                used['strip:' + names[yi]] = used.get('strip:' + names[yi], 0) + 1
            pcs.append((P, cert))
        D['tmpls'][j] = (F(3, 1000), pcs)
    # Lambda_fin from the data (the check re-verifies it per member)
    lam = sum(X.mass(D['alpha0'], *D['tmpls'][j]) for j in (1, 2)) / 2
    D['Lam'] = lam
    return D, names, raws_by_class(), used

def raws_by_class():
    pre = sum((parse(n) for n in PRE), [])
    return {j: pre + sum((parse(n) for n in PROF[j]), []) for j in (1, 2)}

if __name__ == '__main__':
    D, names, raws, used = build()
    why = []
    ok, st = X.check(D, why)
    print('accepted' if ok else 'REJECTED', why[:10])
    print('pieces', {j: len(D['tmpls'][j][1]) for j in D['tmpls']}, 'Lam', D['Lam'], float(D['Lam']))
    print('max R_P', float(st['max_R_P']), 'max C_needed', float(st['max_C_needed']))
    print('branch usage', json.dumps(used))
    wins = sorted({names[c[0]] for j in D['tmpls'] for _, c in D['tmpls'][j][1] if names[c[0]].startswith('W')} |
                  {names[y] for j in D['tmpls'] for _, c in D['tmpls'][j][1] for _, y, _ in c[2] if names[y].startswith('W')})
    print('windows used', wins)
