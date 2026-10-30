"""Independent mirror for gen_bank.py (lane B, package B0).

Does NOT import gen_bank.  Re-derives every emitted value from the receipt with separately written code,
parses the emitted Lean modules (raw_ints% tapes), decodes them, asserts equality with the re-derivation, and then
runs a Python transcription of D5's `SplineData.basicOk` on the decoded data.  Also reports 2-adic hazards
(literals divisible by 2^64).

Usage: python -I mirror_bank.py <Name>
"""
import json, re, sys, os
from fractions import Fraction as Fr
from math import comb, isqrt

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
PROG = os.path.abspath(os.path.join(ROOT, '..', '..', 'outputs', 'Compatibility programme'))
HY = os.path.join(PROG, 'hybrid-exact-receipts-2026-10-27')
SV = os.path.join(PROG, 'sevenths-decay-2026-10-27', 'exact-check')
OUT = os.path.join(ROOT, 'CatalanCore', 'Uniform', 'Bank', 'Common', 'Data')

SRC = {
    'Fifths': (f'{HY}/exact-FIFTH.json', f'{HY}/hyp-FIFTH.json', ['fifth-1', 'fifth-2', 'fifth-3', 'fifth-4']),
    'Thirds': (f'{HY}/exact-THIRD.json', f'{HY}/hyp-THIRD.json', ['thirds+', 'thirds-']),
    'Chi3': (f'{HY}/exact-CHI3.json', f'{HY}/hyp-CHI3.json', ['chi3']),
    'Fourths': (f'{HY}/exact-LAMB.json', f'{HY}/hyp-LAMB.json', ['lambda+', 'lambda-']),
    'Sev1': (f'{SV}/exact-A-tight.json', f'{SV}/hypotheses/hyp-results.json', ['1']),
}


def tapes(path):
    """all `name := ... raw_ints% [ ... ]` tapes of a file, in order, as (declname, [ints])"""
    txt = open(path, encoding='utf-8').read()
    res = []
    for m in re.finditer(r'def\s+(\w+)\s*(?::[^=]*)?:=\s*(?:\w+\s+)?raw_ints%\s*\[([^\]]*)\]', txt):
        res.append((m.group(1), [int(x) for x in m.group(2).replace('\n', ' ').split(',') if x.strip()]))
    return txt, res


def rats(t):
    assert len(t) % 2 == 0
    return [Fr(t[i], t[i + 1]) for i in range(0, len(t), 2)]


def bern_max_via_basis_change(c):
    """max Bernstein coefficient, via explicit matrix inverse of the Bernstein->monomial map (differs from the generator)."""
    n = len(c) - 1
    # b_k = sum_i C(k,i)/C(n,i) c_i ; recompute through the blossom: b_k = blossom(c)(0^(n-k),1^k)
    # blossom by de Casteljau on the "polar form": use dual basis formula with falling factorials
    out = []
    for k in range(n + 1):
        out.append(sum(Fr(comb(k, i) * comb(n - i, 0), 1) / comb(n, i) * c[i] for i in range(k + 1)))
    return out


def main(name):
    exf, hyf, members = SRC[name]
    ex = json.load(open(exf))
    hy = json.load(open(hyf))
    d0 = os.path.join(OUT, name)
    errs = []

    def chk(cond, msg):
        if not cond:
            errs.append(msg)

    # ---- Segs
    txt, tps = tapes(os.path.join(d0, 'Segs.lean'))
    pcs = ex['certificate']['pieces']
    chk(len(tps) == len(pcs), 'piece count')
    segs = []
    for (nm, t), p in zip(tps, pcs):
        tau = t[0]
        r = rats(t[1:])
        ax, ay, bx, by, M, Lq = r[:6]
        coef = r[6:]
        chk(ax == Fr(p['A'][0]) and ay == Fr(p['A'][1]), nm + ' A')
        chk(bx == Fr(p['B'][0]) and by == Fr(p['B'][1]), nm + ' B')
        chk(coef == [Fr(x) for x in p['coefficients']], nm + ' coef')
        # independent M, Lq expectations
        bm = max(bern_max_via_basis_change(coef))
        expM = Fr(-((-bm * 10**10).__ceil__()), 10**10) if False else Fr(-((-(bm * 10**10).numerator) // (bm * 10**10).denominator), 10**10)
        chk(M == expM, nm + ' M')
        c2 = (bx - ax) ** 2 + (by - ay) ** 2
        k = isqrt(int(c2 * 10**20))  # floor(sqrt(c2*1e20)); c2*1e20 may be non-integer: int() truncs (floor, c2>=0)
        expL = Fr(k, 10**10)
        chk(Lq == expL, nm + ' Lq')
        chk(Lq ** 2 <= c2 and Lq > 0, nm + ' Lq<=chord')
        segs.append(dict(tau=tau, ax=ax, ay=ay, bx=bx, by=by, M=M, Lq=Lq, coef=coef))
    n = len(segs)
    # ---- basicOk transcription: segOk, conjOk, mass
    Rc = Fr(2)
    for i, s in enumerate(segs):
        bc = bern_max_via_basis_change(s['coef'])
        chk(all(0 <= b <= s['M'] for b in bc), f'segOk bern {i}')
        chk(all(0 <= sum(c * (Fr(j, 1000) ** e) for e, c in enumerate(s['coef'])) <= s['M'] for j in range(1001)), f'segOk sampled {i}')
        chk((s['ax'], s['ay']) != (s['bx'], s['by']), f'segOk A!=B {i}')
        chk(0 < s['Lq'] and 0 <= s['M'] and s['Lq'] ** 2 <= (s['bx'] - s['ax']) ** 2 + (s['by'] - s['ay']) ** 2, f'segOk L {i}')
        chk(s['ax'] ** 2 + s['ay'] ** 2 <= Rc ** 2 and s['bx'] ** 2 + s['by'] ** 2 <= Rc ** 2, f'segOk radius {i}')
        chk(s['tau'] < n, f'segOk tau {i}')
        t = segs[s['tau']]
        chk(t['ax'] == s['ax'] and t['ay'] == -s['ay'] and t['bx'] == s['bx'] and t['by'] == -s['by'] and t['coef'] == s['coef']
            and t['tau'] == i, f'conjOk {i}')
    mass = sum(sum(c / (j + 1) for j, c in enumerate(s['coef'])) for s in segs)
    chk(mass == 1, f'mass {mass}')
    BsQ = sum(s['M'] / s['Lq'] for s in segs)
    # ---- Cells
    def cells_of(path, prefix, width, keys):
        txt, tp = tapes(path)
        out = {}
        for key in keys:
            blocks = [t for (nm, t) in tp if re.fullmatch(prefix.format(k=key) + r'\d\d', nm)]
            out[key] = [x for b in blocks for x in b]
        return out

    ct = cells_of(os.path.join(d0, 'Cells.lean'), '{k}B', 4, ['ray', 'line'])
    it = cells_of(os.path.join(d0, 'CellInfo.lean'), '{k}I', 9, ['ray', 'line', 'seg'])
    cover = {}
    for key in ('ray', 'line'):
        r = rats(ct[key])
        cover[key] = [(r[i], r[i + 1]) for i in range(0, len(r), 2)]
    for key in ('ray', 'line', 'seg'):
        cells = ex['covers'][key]
        t = it[key]
        chk(len(t) == 9 * len(cells), f'info len {key}')
        for j, c in enumerate(cells):
            e = t[9 * j:9 * j + 9]
            ok = (Fr(e[0], e[1]) == Fr(c[0]) and Fr(e[2], e[3]) == Fr(c[1]) and e[4] == {'endpoint': 0, 'logjet8': 1}[c[2]]
                  and Fr(e[5], e[6]) == Fr(c[3]) and Fr(e[7], e[8]) == Fr(c[4]))
            chk(ok, f'info {key} {j}')
            if key in cover:
                chk(cover[key][j] == (Fr(c[0]), Fr(c[1])), f'cell {key} {j}')
        if key in cover:
            chk(len(cover[key]) == len(cells), f'cell count {key}')

    def cover_ok(a, b, L):
        if not L or not (L[0][0] <= a <= L[0][1]):
            return False
        reach = L[0][1]
        for lo, hi in L[1:]:
            if lo <= reach:
                reach = max(reach, hi)
        return b <= reach
    umax = Fr(ex['tail']['Y'])
    chk(cover_ok(Fr(0), umax, cover['ray']), 'ray cover')
    chk(cover_ok(Fr(0), Fr(1), cover['line']), 'line cover')
    # ---- scalars
    txt, _ = tapes(os.path.join(d0, 'Data.lean'))
    sc = {}
    for m in re.finditer(r'def s_(\w+) : ℚ := q1 \(raw_ints% \[(-?\d+), (\d+)\]\)', txt):
        sc[m.group(1)] = Fr(int(m.group(2)), int(m.group(3)))
    alpha = Fr(ex['alpha'])
    exp = dict(sl=Fr(hy['polygon']['tail_slope']), Mq=1 + alpha, eps=Fr(1, 1000), r0=Fr(ex['trial']['r0']), W=Fr(1, 10**15),
               umax=umax, mprime=Fr(ex['m_cont']), gmin=Fr(ex['targets']['line']), Scap=Fr(ex['S_lower_unit']),
               Ibound=Fr(ex['I_upper']), ccert=Fr(ex['c_upper']), rho=Fr(ex['atom']['rho']), theta=Fr(ex['atom']['mesh_upper']),
               etaS=Fr(ex['cap_bridge']['Sbase_debit']), Rc=Rc, Inu=Fr(ex['Inu_lower']))
    for k, v in exp.items():
        chk(sc.get(k) == v, f'scalar {k}: {sc.get(k)} vs {v}')
    lossS = sc['lossS']
    need = Fr(315, 100) * sc['rho'] * BsQ
    chk(need <= lossS < need + Fr(1, 10**16), 'lossS minimal grid')
    chk(f'dim := {ex["d"]}' in txt, 'dim')
    # dofOk
    V = 1
    Mq, mp, dim = sc['Mq'], sc['mprime'], ex['d']
    rhs = (2 * (Mq * mp + dim * sc['Scap']) - Mq ** 2 * sc['Ibound'] + sc['Inu']
           - (2 * Mq ** 2 * (lossS + sc['theta']) + 2 * dim * sc['etaS'] + Mq ** 2 * (V * lossS + 2 * V * sc['theta'])))
    Dr = Fr(ex['D_lower'])
    adjusted = Dr > rhs
    chk(sc['Dt'] == (Fr((rhs * 10**15).__floor__(), 10**15) if adjusted else Dr), 'Dt = D_lower or floor(rhs)')
    chk(sc['Dt'] <= rhs, f'dofOk: Dt {float(sc["Dt"])} rhs {float(rhs)}')
    chk(0 < Mq and 0 < sc['eps'] < 1 and 0 < sc['r0'] and 0 < sc['W'] and 0 < sc['rho'] and 0 < sc['theta'] and 0 < sc['etaS']
        and 0 <= Rc and 0 <= sc['ccert'] and 2 * (mp - sc['gmin']) <= sc['ccert'], 'basicOk positivity / c')
    # ---- Frame
    txt = open(os.path.join(d0, 'Frame.lean'), encoding='utf-8').read()
    tp = [(None, [int(x) for x in g.replace(chr(10), ' ').split(',') if x.strip()])
          for g in re.findall(r'raw_ints%\s*\[([^\]]*)\]', txt)]
    hyframes = hy['frames']
    ptx = txt
    # members: tapes appear in order shifts, coeffs per member; names are not unique -> use sequence
    seq = [t for nm, t in tp]
    for i, m in enumerate(members):
        pc = hyframes[m]['poles_shift_coeff']
        chk(rats(seq[2 * i]) == [Fr(a) for a, b in pc], f'member {m} shifts')
        chk(rats(seq[2 * i + 1]) == [Fr(b) for a, b in pc], f'member {m} coeffs')
        chk(sum(Fr(b) for a, b in pc) == 0, f'member {m} weights sum')
    ref = hy['reference_geometry']
    def blk(s):
        return [Fr(int(x)) / Fr(int(y)) for x, y in re.findall(r'Fraction\((-?\d+), (\d+)\)', s)]
    base = 2 * len(members) + 1          # skip the alpha tape
    rt = rats(seq[base]); ct_ = rats(seq[base + 1])
    chk(rt == blk(ref['rows']) and ct_ == blk(ref['cols']), 'geometry blocks')
    chk(len(rt) == 6, 'geometry has 2 blocks')
    chk(rats(seq[2 * len(members)]) == [alpha], 'alpha')
    chk(f'selectorPair := {"true" if ref["selector"] == "pair" else "false"}' in txt, 'selector')
    v = rats(seq[base + 2])
    pv = hy['polygon']['vertices']
    chk(v == [Fr(x) for p in pv for x in p], 'polygon vertices')
    # polygon hypotheses transcription: base (-r0, 0), upper strictly increasing Im
    chk(pv[0][1] == '0' and Fr(pv[0][0]) == -sc['r0'], 'polygon base at -r0')
    ims = [Fr(p[1]) for p in pv]
    chk(all(ims[i] < ims[i + 1] for i in range(len(ims) - 1)) and all(x > 0 for x in ims[1:]), 'polygon Im increasing')
    chk(Fr(hy['polygon']['tail_slope']) * -Fr(hy['polygon']['tail_lean']) == 1, 'tail slope * lean = -1')
    # 2-adic hazard scan over every emitted tape
    haz = 0
    tot = 0
    for fn in os.listdir(d0):
        _, tp2 = tapes(os.path.join(d0, fn))
        for nm, t in tp2:
            for x in t:
                tot += 1
                if x != 0 and x % (1 << 64) == 0:
                    haz += 1
    # gather statistics
    stats = dict(pieces=n, ray=len(cover['ray']), line=len(cover['line']), seg=len(ex['covers']['seg']), BsQ=float(BsQ),
                 lossS=float(lossS), Dt=float(sc['Dt']), DtAdjusted=adjusted, DtShortfall=float(Dr - sc['Dt']), dofSlack=float(rhs - sc['Dt']), literals=tot, hazard64=haz,
                 bytes=sum(os.path.getsize(os.path.join(d0, f)) for f in os.listdir(d0)))
    print(name, 'MIRROR', 'OK' if not errs else 'FAIL', stats)
    for e in errs[:30]:
        print('  ERR', e)
    return not errs


if __name__ == '__main__':
    ok = True
    for nm in sys.argv[1:]:
        ok = main(nm) and ok
    sys.exit(0 if ok else 1)
