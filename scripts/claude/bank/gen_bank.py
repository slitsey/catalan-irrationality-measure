"""Bank data generator (lane B, package B0).

Reads one bank's exact (E) receipts and emits Lean data modules under
CatalanCore/Uniform/Bank/Common/Data/<Name>/ in the format expected by
CatalanCore.Uniform.Decay.Cert.Data.SplineData (D5): raw_ints% tapes, one declaration per
piece / per block of cells.  Rationals are encoded as (num, den) pairs in Int tapes.

Usage:  python -I gen_bank.py <Name> [<Name> ...]     (Name in BANKS)
Independent check:  python -I mirror_bank.py <Name>
"""
import json, sys, os, re
from fractions import Fraction as Fr
from math import isqrt, comb

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))                  # worktree
PROG = os.path.abspath(os.path.join(ROOT, '..', '..', 'outputs', 'Compatibility programme'))
HY = os.path.join(PROG, 'hybrid-exact-receipts-2026-10-27')
SV = os.path.join(PROG, 'sevenths-decay-2026-10-27', 'exact-check')
OUTBASE = os.path.join(ROOT, 'CatalanCore', 'Uniform', 'Bank', 'Common', 'Data')

BANKS = {
    'Fifths': dict(exact=f'{HY}/exact-FIFTH.json', hyp=f'{HY}/hyp-FIFTH.json',
                   members=['fifth-1', 'fifth-2', 'fifth-3', 'fifth-4']),
    'Thirds': dict(exact=f'{HY}/exact-THIRD.json', hyp=f'{HY}/hyp-THIRD.json', members=['thirds+', 'thirds-']),
    'Chi3': dict(exact=f'{HY}/exact-CHI3.json', hyp=f'{HY}/hyp-CHI3.json', members=['chi3']),
    'Lambda': dict(exact=f'{HY}/exact-LAMB.json', hyp=f'{HY}/hyp-LAMB.json', members=['lambda+', 'lambda-']),
    'Sev1': dict(exact=f'{SV}/exact-A-tight.json', hyp=f'{SV}/hypotheses/hyp-results.json', members=['1']),
}

# placeholders fixed by the D5 pilot (not receipt quantities)
EPS = Fr(1, 1000)       # smoothing parameter e < eps
WID = Fr(1, 10**15)     # W (positive width parameter of the pilot)
RC = Fr(2)              # radius bound R_c for all vertices
CELLS_PER_BLOCK = 40
GRID_M = 10**10         # Bernstein bound M_i rounded up to 1e-10
GRID_L = 10**10         # arclength lower bound L_i rounded down to 1e-10
GRID_LOSS = 10**16      # lossS rounded up to 1e-16


def fr(s):
    return Fr(s)


def ceil_grid(x, g):
    n = x * g
    c = n.numerator // n.denominator
    if Fr(c) < n:
        c += 1
    return Fr(c, g)


def floor_sqrt_grid(x2, g):
    """largest k/g with (k/g)^2 <= x2"""
    t = x2 * g * g
    k = isqrt(t.numerator // t.denominator)
    return Fr(k, g)


def bern_coeffs(l):
    n = len(l) - 1
    return [sum(Fr(comb(k, i), comb(n, i)) * l[i] for i in range(k + 1)) for k in range(n + 1)]


def pair(q):
    return [q.numerator, q.denominator]


def parse_blocks(s):
    out = []
    for m in re.finditer(r'Fraction\((-?\d+), (\d+)\), Fraction\((-?\d+), (\d+)\), Fraction\((-?\d+), (\d+)\)', s):
        v = [int(x) for x in m.groups()]
        out.append((Fr(v[0], v[1]), Fr(v[2], v[3]), Fr(v[4], v[5])))
    return out


def derive(name):
    B = BANKS[name]
    ex = json.load(open(B['exact']))
    hy = json.load(open(B['hyp']))
    pieces = ex['certificate']['pieces']
    segs = []
    for p in pieces:
        ax, ay = fr(p['A'][0]), fr(p['A'][1])
        bx, by = fr(p['B'][0]), fr(p['B'][1])
        coef = [fr(c) for c in p['coefficients']]
        bc = bern_coeffs(coef)
        M = ceil_grid(max(bc), GRID_M)
        c2 = (bx - ax) ** 2 + (by - ay) ** 2
        Lq = floor_sqrt_grid(c2, GRID_L)
        segs.append(dict(ax=ax, ay=ay, bx=bx, by=by, coef=coef, M=M, Lq=Lq))
    for i, s in enumerate(segs):
        c = [j for j, t in enumerate(segs) if t['ax'] == s['ax'] and t['ay'] == -s['ay'] and t['bx'] == s['bx']
             and t['by'] == -s['by'] and t['coef'] == s['coef']]
        assert len(c) == 1, (name, i, c)
        s['tau'] = c[0]
    for i, s in enumerate(segs):
        assert segs[s['tau']]['tau'] == i
    BsQ = sum(s['M'] / s['Lq'] for s in segs)
    rho = fr(ex['atom']['rho'])
    theta = fr(ex['atom']['mesh_upper'])
    lossS = ceil_grid(Fr(315, 100) * rho * BsQ, GRID_LOSS)
    d = ex['d']
    Mq = Fr(1) + fr(ex['alpha'])
    ref = hy['reference_geometry']
    assert fr(ref['mass']) == Mq
    sc = dict(
        sl=fr(hy['polygon']['tail_slope']), Mq=Mq, eps=EPS, r0=fr(ex['trial']['r0']), W=WID, umax=fr(ex['tail']['Y']),
        mprime=fr(ex['m_cont']), gmin=fr(ex['targets']['line']), Scap=fr(ex['S_lower_unit']), Ibound=fr(ex['I_upper']),
        ccert=fr(ex['c_upper']), rho=rho, theta=theta, etaS=fr(ex['cap_bridge']['Sbase_debit']), lossS=lossS, Rc=RC,
        Inu=fr(ex['Inu_lower']), Dt=fr(ex['D_lower']))
    # D_t: the receipt's D_lower, lowered (floor to 1e-15) only if the checker's own dofOk expression is below it
    rhs = (2 * (Mq * sc['mprime'] + d * sc['Scap']) - Mq ** 2 * sc['Ibound'] + sc['Inu']
           - (2 * Mq ** 2 * (lossS + theta) + 2 * d * sc['etaS'] + Mq ** 2 * (lossS + 2 * theta)))
    sc['Dreceipt'] = sc['Dt']
    if sc['Dt'] > rhs:
        n15 = rhs * 10**15
        sc['Dt'] = Fr(n15.numerator // n15.denominator, 10**15)
    covers = {}
    for key in ('ray', 'line', 'seg'):
        cells = []
        for c in ex['covers'][key]:
            rule = {'endpoint': 0, 'logjet8': 1}[c[2]]
            cells.append(dict(a=fr(c[0]), b=fr(c[1]), rule=rule, lo=fr(c[3]), hi=fr(c[4])))
        covers[key] = cells
    members = []
    for m in B['members']:
        fm = hy['frames'][m]
        pc = [(fr(a), fr(b)) for a, b in fm['poles_shift_coeff']]
        members.append(dict(name=m, shifts=[a for a, _ in pc], coeffs=[b for _, b in pc]))
        assert sum(b for _, b in pc) == 0
    geom = dict(alpha=fr(ex['alpha']), d=d, pair=(ref['selector'] == 'pair'),
                rows=parse_blocks(ref['rows']), cols=parse_blocks(ref['cols']))
    poly = dict(vertices=[(fr(a), fr(b)) for a, b in hy['polygon']['vertices']],
                tailSlope=fr(hy['polygon']['tail_slope']), tailLean=fr(hy['polygon']['tail_lean']))
    price = ex.get('price')
    return dict(name=name, d=d, gamma=fr(ex['gamma']), segs=segs, sc=sc, covers=covers, members=members, geom=geom,
                poly=poly, price=(fr(price['rational']), fr(price['log2'])) if price else None)


# ---------------- Lean emission ----------------
def tape(ints, per=24):
    toks = [str(x) for x in ints]
    lines = [', '.join(toks[i:i + per]) for i in range(0, len(toks), per)]
    return 'raw_ints% [\n    ' + ',\n    '.join(lines) + ']'


def seg_tape(s):
    t = [s['tau']]
    for k in ('ax', 'ay', 'bx', 'by', 'M', 'Lq'):
        t += pair(s[k])
    for c in s['coef']:
        t += pair(c)
    return t


def cell_tape(c):
    return pair(c['a']) + pair(c['b'])


def info_tape(c):
    return pair(c['a']) + pair(c['b']) + [c['rule']] + pair(c['lo']) + pair(c['hi'])


HEAD = 'import CatalanCore.Uniform.Bank.Common.Schema\n\nnamespace CatalanCore.Uniform.Bank.Common.Data.{N}\nopen CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert\n\n'
FOOT = '\nend CatalanCore.Uniform.Bank.Common.Data.{N}\n'


PILOT = '''import CatalanCore.Uniform.Bank.Common.Data.@N@.Data

/-! Pilot (lane B, B0), generated: D5's elementary checker `basicOk` on the @N@ bank data, timed per declaration. -/

namespace CatalanCore.Uniform.Bank.Common.Pilot.@N@

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Bank.Common.Data.@N@

set_option maxRecDepth 100000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 5

theorem @n@_segOk : ((List.finRange data.n).all data.segOk) = true := by decide +kernel
theorem @n@_conjOk : ((List.finRange data.n).all data.conjOk) = true := by decide +kernel
theorem @n@_mass : (∑ i : Fin data.n, SplineData.massOf (data.l i) = 1) := by decide +kernel
theorem @n@_loss : (315 / 100 : ℚ) * data.rho * data.BsQ ≤ data.lossS := by decide +kernel
theorem @n@_rayCover : coverOk 0 data.umax data.rayBoxes = true := by decide +kernel
theorem @n@_lineCover : coverOk 0 1 data.lineCells = true := by decide +kernel
theorem @n@_dof : data.dofOk = true := by decide +kernel
theorem @n@_basicOk : data.basicOk = true := by decide +kernel

end CatalanCore.Uniform.Bank.Common.Pilot.@N@
'''


def q1(q):
    return f'q1 (raw_ints% [{q.numerator}, {q.denominator}])'


def emit(name):
    D = derive(name)
    N = name
    out = os.path.join(OUTBASE, N)
    os.makedirs(out, exist_ok=True)
    mods = {}
    s = HEAD.format(N=N) + '/-! Generated by scripts/claude/bank/gen_bank.py; do not edit. -/\n\n'
    for i, sg in enumerate(D['segs']):
        s += f'def seg{i:02d} : Seg := decodeSeg {tape(seg_tape(sg))}\n\n'
    s += 'def segs : List Seg := [' + ', '.join(f'seg{i:02d}' for i in range(len(D['segs']))) + ']\n'
    mods['Segs'] = s + FOOT.format(N=N)
    s = HEAD.format(N=N) + '/-! Generated; ray/line cover cells as (a, b) pairs, blocks of %d. -/\n\n' % CELLS_PER_BLOCK
    for key in ('ray', 'line'):
        cells = D['covers'][key]
        nb = (len(cells) + CELLS_PER_BLOCK - 1) // CELLS_PER_BLOCK
        for b in range(nb):
            blk = cells[b * CELLS_PER_BLOCK:(b + 1) * CELLS_PER_BLOCK]
            ints = [x for c in blk for x in cell_tape(c)]
            s += f'def {key}B{b:02d} : List (ℚ × ℚ) := cellsOf {tape(ints, 16)}\n\n'
        s += f'def {key}Cells : List (ℚ × ℚ) := ' + ' ++ '.join(f'{key}B{b:02d}' for b in range(nb)) + '\n\n'
    mods['Cells'] = s + FOOT.format(N=N)
    s = HEAD.format(N=N) + ('/-! Generated; per-cell rule code (0 endpoint, 1 logjet8) and receipt enclosure '
                            '[lo, hi] of the potential. -/\n\n')
    for key in ('ray', 'line', 'seg'):
        cells = D['covers'][key]
        nb = (len(cells) + CELLS_PER_BLOCK - 1) // CELLS_PER_BLOCK
        for b in range(nb):
            blk = cells[b * CELLS_PER_BLOCK:(b + 1) * CELLS_PER_BLOCK]
            ints = [x for c in blk for x in info_tape(c)]
            s += f'def {key}I{b:02d} : List CellInfo := infoOf {tape(ints, 18)}\n\n'
        s += f'def {key}Info : List CellInfo := ' + ' ++ '.join(f'{key}I{b:02d}' for b in range(nb)) + '\n\n'
    mods['CellInfo'] = s + FOOT.format(N=N)
    sc = dict(D['sc'])
    sc.pop('Dreceipt')
    s = ('import CatalanCore.Uniform.Bank.Common.Data.%s.Segs\nimport CatalanCore.Uniform.Bank.Common.Data.%s.Cells\n\n'
         % (N, N))
    s += (f'namespace CatalanCore.Uniform.Bank.Common.Data.{N}\n'
          'open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert\n\n')
    s += '/-! Generated; scalar certificate numbers and the assembled `SplineData`. -/\n\n'
    for k in ('sl', 'Mq', 'eps', 'r0', 'W', 'umax', 'mprime', 'gmin', 'Scap', 'Ibound', 'ccert', 'rho', 'theta', 'etaS',
              'lossS', 'Rc', 'Inu', 'Dt'):
        s += f'def s_{k} : ℚ := {q1(sc[k])}\n'
    s += '\ndef data : SplineData where\n  segs := segs\n  sl := s_sl\n  Mq := s_Mq\n  ε := s_eps\n  r0 := s_r0\n  W := s_W\n  umax := s_umax\n'
    s += '  mprime := s_mprime\n  gmin := s_gmin\n  Scap := s_Scap\n  Ibound := s_Ibound\n  ccert := s_ccert\n  rayBoxes := rayCells\n'
    s += ('  lineCells := lineCells\n  rho := s_rho\n  theta := s_theta\n  etaS := s_etaS\n  lossS := s_lossS\n  Rc := s_Rc\n'
          f'  Inu := s_Inu\n  Dt := s_Dt\n  dim := {D["d"]}\n')
    mods['Data'] = s + FOOT.format(N=N)
    g = D['geom']
    po = D['poly']
    s = HEAD.format(N=N) + ('/-! Generated; frame members (shifts, coefficients), block geometry (alpha, blocks) '
                            'and polygon. -/\n\n')
    for i, m in enumerate(D['members']):
        ints = [x for q in m['shifts'] for x in pair(q)]
        ints2 = [x for q in m['coeffs'] for x in pair(q)]
        s += f'def member{i} : FrameMember where\n  shifts := ratsOf {tape(ints)}\n  coeffs := ratsOf {tape(ints2)}\n\n'
    s += 'def members : List FrameMember := [' + ', '.join(f'member{i}' for i in range(len(D['members']))) + ']\n\n'

    def blocks(bs):
        return [x for (lo, hi, de) in bs for q in (lo, hi, de) for x in pair(q)]
    s += (f'def geom : GeomData where\n  alpha := {q1(g["alpha"])}\n  dim := {g["d"]}\n'
          f'  selectorPair := {"true" if g["pair"] else "false"}\n')
    s += f'  rows := blocksOf {tape(blocks(g["rows"]))}\n  cols := blocksOf {tape(blocks(g["cols"]))}\n\n'
    vi = [x for (a, b) in po['vertices'] for q in (a, b) for x in pair(q)]
    s += (f'def polygon : PolygonData where\n  vertices := vertsOf {tape(vi)}\n  tailSlope := {q1(po["tailSlope"])}\n'
          f'  tailLean := {q1(po["tailLean"])}\n\n')
    if D['price']:
        s += (f'def price : ℚ × ℚ := ({q1(D["price"][0])}, {q1(D["price"][1])})'
              '  -- (rational part, coefficient of log 2)\n')
    mods['Frame'] = s + FOOT.format(N=N)
    pil = os.path.join(os.path.dirname(OUTBASE), 'Pilot')
    os.makedirs(pil, exist_ok=True)
    with open(os.path.join(pil, N + '.lean'), 'w', encoding='utf-8', newline=chr(10)) as f:
        f.write(PILOT.replace('@N@', N).replace('@n@', N.lower()))
    for k, v in mods.items():
        with open(os.path.join(out, k + '.lean'), 'w', encoding='utf-8', newline='\n') as f:
            f.write(v)
    return D


if __name__ == '__main__':
    for nm in sys.argv[1:]:
        D = emit(nm)
        print(nm, 'pieces', len(D['segs']), 'ray', len(D['covers']['ray']), 'line', len(D['covers']['line']),
              'seg', len(D['covers']['seg']))
