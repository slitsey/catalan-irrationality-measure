"""Fifths no-UF strict profile with per-piece provenance (lane B, B5c).
Writes nouf-meta.json: for each kappa index j=1..4 the pieces of min(T,LP,M3D) (R never strictly needed:
dropping R leaves the exact rational Lambda unchanged), with
  M3D : cut-gap numerals (n0,n1,n3) of the segment between consecutive cuts of the families t=0,t=k,t=r (mod p)
  T   : kind in saw/D3/D2/D45/D6 (matched against the closed forms)
  LP  : (to be filled)
Checks: reproduces replay-fifths noUF rational exactly; every M3D piece line equals the formula line."""
from pathlib import Path
from fractions import Fraction as Q
import json, sys, math
sys.dont_write_bytecode = True
R = Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform')
P = R.parents[1] / 'outputs/Compatibility programme'
sys.path.insert(0, str(P / 'hybrid-alpha-2026-10-27'))
import _paths
sys.path.insert(0, str(P / 'q4-mechanisms-uniform-2026-10-27'))
sys.path.insert(0, str(R / 'scripts/claude/bank/fifths'))
import newprice as N, m3
UF = len(sys.argv) > 1 and sys.argv[1] == 'uf'
if UF:
    import closed as CL
    prevsc = json.load(open(P / 'scope-screen-2026-10-27/s-q5-a1-alpha1_9-lo2_9.json'))
    ctx = N.context(5, 1, Q(1, 9))
Line = N.Line
al = Q(1, 9); left = 2 * al; hi3 = 1 + 4 * al; Nn = 1 + 2 * al
right = Q(55, 9)
D = json.loads((P / 'bank-specs-2026-10-28/rank-fifths.json').read_text())
jmap = {c['prime_class']: int(Q(c['pole_cut']) * 5) for c in D['cases']}


def p3_candidates(ka, u, v):
    """P3 candidate lines with provenance: (line, A, B, wl, wh)."""
    mid = (u + v) / 2
    cuts = m3.lines_for(al, ka, u, v)
    lo_w = [Line(Q(1), Q(0)), Line(1 + 2 * al, Q(-1))]; hi_w = [Line(1 + 2 * al, Q(0)), Line(Q(1), Q(1))]
    wl = max(lo_w, key=lambda f: f(mid)); wh = min(hi_w, key=lambda f: f(mid))
    pos = sorted(cuts, key=lambda f: f(mid))
    out = []
    for A, B in zip(pos, pos[1:]):
        if B(mid) <= A(mid): continue
        a = max([A, wl], key=lambda f: f(mid)); b = min([B, wh], key=lambda f: f(mid))
        if b(mid) > a(mid):
            out.append((Line(2 + 2 * al - (b.intercept - a.intercept), -(b.slope - a.slope)), A, B, wl, wh))
    return out


def fam(line):
    """family of a cut line: ('z0',n) slope n int; ('z1',n) slope n+ka; ('z3',j) intercept 1."""
    return line


def numerals(ka, A, B, wl, wh, mid):
    a = max([A, wl], key=lambda f: f(mid)); b = min([B, wh], key=lambda f: f(mid))
    av, bv = a(mid), b(mid)
    n0 = math.floor(av / mid)
    n1 = math.floor(av / mid - ka)
    n3 = math.floor((av - 1) / mid)
    # gap checks at mid
    assert n0 * mid <= av and bv <= (n0 + 1) * mid, ('F0', n0)
    assert (n1 + ka) * mid <= av and bv <= (n1 + 1 + ka) * mid, ('F1', n1)
    assert 1 + n3 * mid <= av and bv <= 1 + (n3 + 1) * mid, ('F3', n3)
    return n0, n1, n3


def formula_line(ka, n0, n1, n3):
    """The line of the integer formula (2r+2m-(Bu-a)) for the cut-gap numerals, as a function of theta."""
    def f(th):
        a = max(n0 * th, (n1 + ka) * th, 1 + n3 * th, Q(1), Nn - th)
        b = min((n0 + 1) * th, (n1 + 1 + ka) * th, 1 + (n3 + 1) * th, Nn, 1 + th)
        return 2 + 2 * al - max(b - a, Q(0))
    return f


def t_kind(ka, line, u, v):
    mid = (u + v) / 2; k = ka
    cands = {}
    cands['D3'] = Line(2 + al, Q(0))
    # saw with m<p<2m : 2+3al-theta
    cands['saw0'] = Line(2 + 3 * al, Q(-1))
    # D2 (x=(1+k)th-1): x<=2al: 3+2al-(1+k)th ; x>=2al: 2+4al-2x = 4+4al-2(1+k)th
    cands['D2a'] = Line(3 + 2 * al, -(1 + k))
    cands['D2b'] = Line(4 + 4 * al, -2 * (1 + k))
    cands['D45'] = Line(3 + 4 * al, -(2 * k + 1))
    cands['D45z'] = Line(2 + 2 * al, -2 * k)
    cands['D6'] = Line(1 + 2 * al, -k)
    for name, c in cands.items():
        if c.intercept == line.intercept and c.slope == line.slope: return name
    return None


def scan_cand(j, ka, a, b, f):
    A, B = float(f.intercept), float(f.slope)
    worst = {}; qs = set()
    for r in (2000000, 2000010, 3000002):
        m = CL.border(r)
        step = max(1, int((b - a) * r) // 220)
        for u in (1, 2, 3, 4):
            for p in range(int(a * r) + 1, int(b * r) + 1, step):
                if (j * p + u) % 5: continue
                k = (j * p + u) // 5
                qs.add(r // p)
                line = A * r + B * p
                for kk in (False, True):
                    for zz in (False, True):
                        dv = CL.candPrice(m, r, p, k, kk, zz) - line
                        worst[(kk, zz)] = max(worst.get((kk, zz), -1e18), dv)
    good = [kz for kz, w in worst.items() if w <= 6]
    assert len(good) == 1 and len(qs) == 1, (j, a, b, good, qs, worst)
    return dict(kappa=good[0][0], zeta=good[0][1], q=sorted(qs)[0])


out = {}
for case in D['cases']:
    j = jmap[case['prime_class']]
    ka = Q(case['pole_cut'])
    rank = [(Q(v['left']), Q(v['right']), Line(Q(v['line'][0]), Q(v['line'][1]))) for c in case['cells'] for v in c['price_pieces']]
    cuts = {al, left, right, hi3} | {x for x in N.breakpoints(al, ka) if left < x < right} | {x for x in N.g_kinks(al, ka) if left < x < right}
    cuts |= {x for u, v, f in rank for x in (u, v)}
    Spcs = []
    if UF:
        Spcs = N.pieces_of(N.formula_band(ctx, left, right, case['prime_class'], limits=N.LIM)['cells'], 'price_upper_pieces')
        cuts |= {x for u, v, f in Spcs for x in (u, v)}
    fine = set(cuts)
    for u, v in zip(sorted(cuts), sorted(cuts)[1:]):
        if u < hi3: fine |= m3.kinks(al, ka, u, min(v, hi3))
    fine = sorted(x for x in fine if al <= x <= right)
    pieces = []
    for u, v in zip(fine, fine[1:]):
        mid = (u + v) / 2
        T = Line(2 + 3 * al, Q(-1)) if mid < left else N.trop_line(u, v, al, ka)
        ls = [('T', T, None)]
        if mid >= left:
            g = N.g_line(mid, al, ka)
            if 1 < mid and ka * mid < 1 and (1 + ka) * mid < 1 + 2 * al: g = Line(Q(0), Q(0))
            ls.append(('LP', Line(T.intercept - g.intercept, T.slope - g.slope), None))
        if mid < hi3:
            for (ln, A, B, wl, wh) in p3_candidates(ka, u, v): ls.append(('M3D', ln, (A, B, wl, wh)))
        if UF and mid >= left:
            ls.append(('S', next(f for a_, b_, f in Spcs if a_ < mid < b_), None))
        sub = {u, v}
        for _, f, _m in ls:
            for _, g, _m2 in ls:
                if f.slope != g.slope:
                    x = (g.intercept - f.intercept) / (f.slope - g.slope)
                    if u < x < v: sub.add(x)
        for a, b in zip(sorted(sub), sorted(sub)[1:]):
            md = (a + b) / 2
            tag, f, meta = min(ls, key=lambda t: t[1](md))
            assert f(a) >= 0 and f(b) >= 0
            rec = dict(left=str(a), right=str(b), line=[str(f.intercept), str(f.slope)], layer=tag)
            if tag == 'M3D':
                A, B, wl, wh = meta
                n0, n1, n3 = numerals(ka, A, B, wl, wh, md)
                fl = formula_line(ka, n0, n1, n3)
                for t_ in (a + (b - a) / 7, md, b - (b - a) / 7):
                    assert fl(t_) == f(t_), ('formula mismatch', j, a, b, t_, fl(t_), f(t_))
                rec['meta'] = dict(n0=n0, n1=n1, n3=n3)
            elif tag == 'S':
                rec['meta'] = dict(cand=scan_cand(j, ka, a, b, f))
            elif tag == 'T':
                kd = t_kind(ka, f, a, b)
                rec['meta'] = dict(kind=kd)
            if pieces and pieces[-1]['line'] == rec['line'] and pieces[-1]['right'] == rec['left'] and pieces[-1]['layer'] == tag and pieces[-1].get('meta') == rec.get('meta'):
                pieces[-1]['right'] = rec['right']
            else:
                pieces.append(rec)
    mass = sum((Q(v['line'][0]) * (Q(v['right']) - Q(v['left'])) + Q(v['line'][1]) * (Q(v['right']) ** 2 - Q(v['left']) ** 2) / 2 for v in pieces), Q(0))
    out[j] = dict(j=j, prime_class=case['prime_class'], kappa=str(ka), pieces=pieces, mass=str(mass))
prefix = 4 * al + 2 * al ** 2 - ((2 + 3 * al) * al - Q(3, 2) * al ** 2)
A_ = prefix + sum((Q(c['mass']) for c in out.values()), Q(0)) / 4
expected = Q(json.loads((P / 'bank-specs-2026-10-28/replay-fifths.json').read_text())['UF' if UF else 'noUF']['rational'])
assert A_ == expected, (A_, expected)
(R / ('scripts/claude/bank/fifths/%s-meta.json' % ('uf' if UF else 'nouf'))).write_text(json.dumps(dict(prefix=str(prefix), lam=str(A_), classes=out), indent=1), encoding='utf-8')
from collections import Counter
for j, c in out.items():
    print(j, len(c['pieces']), dict(Counter(p['layer'] for p in c['pieces'])), dict(Counter(p['meta']['kind'] for p in c['pieces'] if p['layer'] == 'T')))
