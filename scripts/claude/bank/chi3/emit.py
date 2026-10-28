"""B3b emitter: generator outputs (Gen.lean / Gen2.lean) -> Lean modules under CatalanCore/Uniform/Bank/Chi3/.

usage: python -I emit.py <scratch dir with gen_*.out, gen2_E_*.out, gen2_G.out>
"""
import sys, os, glob, re
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..'))
sys.path.insert(0, os.path.join(HERE, '..'))
import gen_bank
OUT = os.path.join(ROOT, 'CatalanCore', 'Uniform', 'Bank', 'Chi3')
SCR = sys.argv[1]
BLK_TUBE = 10
BLK_LINE = 15
ROWS_PER_MOD = 3

d = gen_bank.derive('Chi3')
sc = d['sc']

def fq(n, dd):
    return Fr(int(n), int(dd))

def tape(ints, per=20):
    toks = [str(x) for x in ints]
    return 'raw_ints% [\n    ' + ',\n    '.join(', '.join(toks[i:i + per]) for i in range(0, len(toks), per)) + ']'

def pair(q):
    return [q.numerator, q.denominator]

# ---------------------------------------------------------------- read generator output
tube = {}; line = []; cap = []
fails = []
for f in sorted(glob.glob(os.path.join(SCR, 'gen_[0-9].out'))):
    for ln in open(f, encoding='utf-8'):
        ln = ln.strip()
        if not ln:
            continue
        if ln.startswith('FAIL'):
            fails.append(ln); continue
        head, *rest = [p.strip() for p in ln.split('|')]
        h = head.split()
        if h[0] == 'T':
            e = int(h[1]); a = fq(h[2], h[3]); b = fq(h[4], h[5])
            tube.setdefault(e, []).append((a, b, [int(x) for x in rest[0].split()]))
        elif h[0] == 'L':
            a = fq(h[1], h[2]); b = fq(h[3], h[4])
            line.append((a, b, [int(x) for x in rest[0].split()]))
        elif h[0] == 'C':
            a = fq(h[1], h[2]); b = fq(h[3], h[4])
            ub = [int(x) for x in rest[0].split()]
            cap.append((a, b, Fr(ub[0], ub[1]), [int(x) for x in rest[1].split()]))
if fails:
    print('FAILS', len(fails)); print('\n'.join(fails[:20])); sys.exit(1)
for e in tube: tube[e].sort(key=lambda t: t[0])
line.sort(key=lambda t: t[0]); cap.sort(key=lambda t: t[0])
for e in range(8):
    cs = tube[e]
    assert cs[0][0] == 0 and cs[-1][1] == 1, (e, cs[0][0], cs[-1][1])
    for x, y in zip(cs, cs[1:]): assert x[1] == y[0], (e, x[1], y[0])
assert line[0][0] == 0 and line[-1][1] == 1
for x, y in zip(line, line[1:]): assert x[1] == y[0]
r0 = sc['r0']
assert cap[0][0] == -r0 and cap[-1][1] == 0
for x, y in zip(cap, cap[1:]): assert x[1] == y[0]
print('tube', {e: len(v) for e, v in tube.items()}, 'line', len(line), 'cap', len(cap))

def cell_tape(a, b, ints):
    return pair(a) + pair(b) + ints

def kind_name(ints):
    return {0: 'far', 1: 'jet', 2: 'mix'}[ints[0]]
from collections import Counter
print(Counter((kind_name(c[2]), c[2][1] if c[2][0] else 0) for e in tube for c in tube[e]))
print('line', Counter((kind_name(c[2]), c[2][1] if c[2][0] else 0) for c in line))

# ---------------------------------------------------------------- energies and G
E = {}
for f in glob.glob(os.path.join(SCR, 'gen2_E_*.out')):
    for ln in open(f, encoding='utf-8'):
        t = ln.split()
        if not t: continue
        if t[0] == 'FAIL': print('E FAIL', ln); sys.exit(1)
        assert t[5] == 'true', ln
        E[(int(t[1]), int(t[2]))] = fq(t[3], t[4])
n = len(d['segs'])
assert len(E) == n * n, len(E)
Esum = sum(E.values())
print('Esum', float(Esum), 'Ibound', float(sc['Ibound']), 'ok', Esum <= sc['Ibound'])
Gl = open(os.path.join(SCR, 'gen2_G.out')).read().split()
G = fq(Gl[1], Gl[2])
m = sc['mprime']
capSum = sum((b - a) * max(ub - m, 0) for a, b, ub, _ in cap)
rhs = G - m * r0
Scap_max = rhs - capSum
print('G', float(G), 'capSum', float(capSum), 'Scap_max', float(Scap_max), 'receipt Scap', float(sc['Scap']))
Scap = min(sc['Scap'], Fr((Scap_max * 10**18).__floor__(), 10**18))
if Scap < sc['Scap']:
    print('Scap lowered by', float(sc['Scap'] - Scap))
# Dt: dofOk rhs with new Scap
Mq = sc['Mq']; dim = d['d']
rhsD = (2 * (Mq * sc['mprime'] + dim * Scap) - Mq ** 2 * sc['Ibound'] + sc['Inu']
        - (2 * Mq ** 2 * (sc['lossS'] + sc['theta']) + 2 * dim * sc['etaS'] + Mq ** 2 * (sc['lossS'] + 2 * sc['theta'])))
Dt = sc['Dt']
if Dt > rhsD:
    Dt = Fr((rhsD * 10**15).__floor__(), 10**15)
print('Dt', float(sc['Dt']), '->', float(Dt))

# ---------------------------------------------------------------- Lean emission
NS = 'CatalanCore.Uniform.Bank.Chi3'
def w(path, s):
    p = os.path.join(OUT, path)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, 'w', encoding='utf-8', newline='\n').write(s)

def q1(q):
    return f'qOfP ({q.numerator}) ({q.denominator})'

# Env: polygon edges, line cells, Dchi
V = d['poly']['vertices']; tmax = Fr(13943, 2000); slope = d['poly']['tailSlope']
L = V[-1]
tail_end = (L[0] - tmax, L[1] + slope * tmax)
pts = V + [tail_end]
edges = list(zip(pts, pts[1:]))
env = f'''import CatalanCore.Uniform.Bank.Common.Data.Chi3.Data
import CatalanCore.Uniform.Bank.Common.Data.Chi3.Frame
import CatalanCore.Uniform.Decay.PolyWire2.Decode
import CatalanCore.Uniform.Decay.PolyFull.Full
set_option Elab.async false

/-! Generated by scripts/claude/bank/chi3/emit.py (lane B, B3b): environment of the chi3 bank tables. -/

namespace {NS}
open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyWire2
  CatalanCore.Uniform.Decay.PolyCells CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells
  CatalanCore.Uniform.Decay.NearCells

def RP : List (ℚ × ℚ × ℚ) := [(1, 0, 1), (1 / 2, 1, 3 / 2)]
def nuC : List Seg := nodeSegs RP RP
def Dbase : SplineData := CatalanCore.Uniform.Bank.Common.Data.Chi3.data
def Pply : RatPolygon := ⟨49 / 500, CatalanCore.Uniform.Bank.Common.Data.Chi3.polygon.vertices.tail, 200 / 191⟩
def tmaxC : ℚ := 13943 / 2000
def Rtw : ℚ := 4
def eWc : ℕ := 50
def ePc : ℕ := 51
def Fc : FarData := ⟨5 / 4 * 2 + 5 / 4 * (3 / 2), 4⟩

/-- Line cells (boundaries of the line table). -/
def lineCellsC : List (ℚ × ℚ) := pairsQ (qsOf {tape([x for (a, b, _) in line for x in pair(a) + pair(b)])})

/-- The data with the line cover of this table, the cap value of this table and the matching `Dt`. -/
def Dchi : SplineData := {{ Dbase with lineCells := lineCellsC, Scap := {q1(Scap)}, Dt := {q1(Dt)} }}
def Dn : SplineData := Dchi.noRay

'''
for i, (p, q) in enumerate(edges):
    env += f'def e{i} : Pt × Pt := (({q1(p[0])}, {q1(p[1])}), ({q1(q[0])}, {q1(q[1])}))\n'
env += f'''
def edgesLit : List (Pt × Pt) := [{', '.join(f'e{i}' for i in range(len(edges)))}]

theorem edges_eq : edgesAll Pply tmaxC = edgesLit := by decide +kernel

end {NS}
'''
w('Env.lean', env)

HEADER = '''import CatalanCore.Uniform.Bank.Chi3.Env
set_option Elab.async false
set_option maxRecDepth 100000

/-! Generated by scripts/claude/bank/chi3/emit.py (lane B, B3b); do not edit. -/

namespace %s
open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.PolyWire CatalanCore.Uniform.Decay.PolyWire2
  CatalanCore.Uniform.Decay.PolyCells CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Uniform.Decay.PolyFull

''' % NS
FOOT = f'\nend {NS}\n'

# ---- tube blocks
edge_blocks = {}
for e in range(8):
    cs = tube[e]
    blocks = [cs[i:i + BLK_TUBE] for i in range(0, len(cs), BLK_TUBE)]
    names = []
    for bi, blk in enumerate(blocks):
        mod = f'Tube/E{e}B{bi:02d}'
        s = HEADER
        for ci, (a, b, ints) in enumerate(blk):
            s += f'def c{e}_{bi:02d}_{ci:02d} : TCell2 := decodeCell {tape(cell_tape(a, b, ints))}\n\n'
            s += (f'theorem ok{e}_{bi:02d}_{ci:02d} : cellOk2 nuC Rtw eWc ePc Fc Dn e{e} c{e}_{bi:02d}_{ci:02d} = true := by\n'
                  '  decide +kernel\n\n')
        lst = ', '.join(f'c{e}_{bi:02d}_{ci:02d}' for ci in range(len(blk)))
        s += f'def blk{e}_{bi:02d} : List TCell2 := [{lst}]\n\n'
        proof = 'allT_nil _'
        for ci in reversed(range(len(blk))):
            proof = f'allT_cons ok{e}_{bi:02d}_{ci:02d} ({proof})'
        s += f'theorem blk{e}_{bi:02d}_ok : blk{e}_{bi:02d}.all (cellOk2 nuC Rtw eWc ePc Fc Dn e{e}) = true :=\n  {proof}\n'
        w(mod + '.lean', s + FOOT)
        names.append((mod, f'blk{e}_{bi:02d}'))
    edge_blocks[e] = names
    s = 'import ' + '\nimport '.join(NS + '.' + m.replace('/', '.') for m, _ in names) + '\n'
    s += HEADER.split('\n', 1)[1]
    cat = ' ++ '.join(b for _, b in names)
    s += f'def ecells{e} : List TCell2 := {cat}\n\n'
    proof = f'{names[-1][1]}_ok'
    for _, b in reversed(names[:-1]):
        proof = f'allT_append {b}_ok ({proof})'
    s += f'theorem ecells{e}_all : ecells{e}.all (cellOk2 nuC Rtw eWc ePc Fc Dn e{e}) = true :=\n  {proof}\n\n'
    s += (f'theorem ecells{e}_cov : coverOk 0 1 (ecells{e}.map fun c => (c.ulo, c.uhi)) = true := by\n'
          '  decide +kernel\n\n')
    s += f'theorem ecells{e}_ok : edgeCells2 (cellOk2 nuC Rtw eWc ePc Fc Dn) e{e} ecells{e} = true :=\n'
    s += f'  edgeCells2_of ecells{e}_cov ecells{e}_all\n'
    w(f'Tube/Edge{e}.lean', s + FOOT)

s = 'import ' + '\nimport '.join(f'{NS}.Tube.Edge{e}' for e in range(8)) + '\n' + HEADER.split('\n', 1)[1]
s += 'def tubeC : List (List TCell2) := [' + ', '.join(f'ecells{e}' for e in range(8)) + ']\n\n'
proof = 'tubeCells2_nil _'
for e in reversed(range(8)):
    proof = f'tubeCells2_cons ecells{e}_ok ({proof})'
s += ('theorem tube_ok : tubeCells2 (cellOk2 nuC Rtw eWc ePc Fc Dn) edgesLit tubeC = true :=\n  ' + proof + '\n')
w('Tube/Top.lean', s + FOOT)

# ---- line blocks
lblocks = [line[i:i + BLK_LINE] for i in range(0, len(line), BLK_LINE)]
lnames = []
for bi, blk in enumerate(lblocks):
    s = HEADER
    for ci, (a, b, ints) in enumerate(blk):
        s += f'def l{bi:02d}_{ci:02d} : TCell2 := decodeCell {tape(cell_tape(a, b, ints))}\n\n'
        s += (f'theorem lok{bi:02d}_{ci:02d} : lineCellOk2 nuC Rtw eWc ePc Dn l{bi:02d}_{ci:02d} = true := by\n'
              '  decide +kernel\n\n')
    s += f'def lblk{bi:02d} : List TCell2 := [' + ', '.join(f'l{bi:02d}_{ci:02d}' for ci in range(len(blk))) + ']\n\n'
    proof = 'allT_nil _'
    for ci in reversed(range(len(blk))):
        proof = f'allT_cons lok{bi:02d}_{ci:02d} ({proof})'
    s += f'theorem lblk{bi:02d}_ok : lblk{bi:02d}.all (lineCellOk2 nuC Rtw eWc ePc Dn) = true :=\n  {proof}\n'
    w(f'Line/B{bi:02d}.lean', s + FOOT)
    lnames.append(f'lblk{bi:02d}')
s = 'import ' + '\nimport '.join(f'{NS}.Line.B{bi:02d}' for bi in range(len(lblocks))) + '\n' + HEADER.split('\n', 1)[1]
s += 'def lineC : List TCell2 := ' + ' ++ '.join(lnames) + '\n\n'
proof = f'{lnames[-1]}_ok'
for b in reversed(lnames[:-1]):
    proof = f'allT_append {b}_ok ({proof})'
s += 'theorem line_all : lineC.all (lineCellOk2 nuC Rtw eWc ePc Dn) = true :=\n  ' + proof + '\n\n'
s += 'theorem line_eq : Dn.lineCells = lineC.map (fun c => (c.ulo, c.uhi)) := by decide +kernel\n'
w('Line/Top.lean', s + FOOT)

# ---- cap
CAPB = 12
cblocks = [cap[i:i + CAPB] for i in range(0, len(cap), CAPB)]
cnames = []
for bi, blk in enumerate(cblocks):
    s = HEADER
    for ci, (a, b, ub, ints) in enumerate(blk):
        s += (f'def k{bi:02d}_{ci:02d} : TCell2 × ℚ := decodeCap {tape(pair(ub))} {tape(cell_tape(a, b, ints))}\n\n')
        s += (f'theorem kok{bi:02d}_{ci:02d} : ubCellOk2 nuC Rtw eWc ePc Dn k{bi:02d}_{ci:02d} = true := by\n'
              '  decide +kernel\n\n')
    s += f'def kblk{bi:02d} : List (TCell2 × ℚ) := [' + ', '.join(f'k{bi:02d}_{ci:02d}' for ci in range(len(blk))) + ']\n\n'
    proof = 'allT_nil _'
    for ci in reversed(range(len(blk))):
        proof = f'allT_cons kok{bi:02d}_{ci:02d} ({proof})'
    s += f'theorem kblk{bi:02d}_ok : kblk{bi:02d}.all (ubCellOk2 nuC Rtw eWc ePc Dn) = true :=\n  {proof}\n'
    w(f'Cap/B{bi:02d}.lean', s + FOOT)
    cnames.append(f'kblk{bi:02d}')
s = 'import ' + '\nimport '.join(f'{NS}.Cap.B{bi:02d}' for bi in range(len(cblocks))) + '\n' + HEADER.split('\n', 1)[1]
s += 'def capC : List (TCell2 × ℚ) := ' + ' ++ '.join(cnames) + '\n\n'
proof = f'{cnames[-1]}_ok'
for b in reversed(cnames[:-1]):
    proof = f'allT_append {b}_ok ({proof})'
s += 'theorem cap_all : capC.all (ubCellOk2 nuC Rtw eWc ePc Dn) = true :=\n  ' + proof + '\n\n'
s += f'def Gcap : ℚ := {q1(G)}\n'
w('Cap/Top.lean', s + FOOT)

# ---- energies: one module per ROWS_PER_MOD rows
emods = []
for r0i in range(0, n, ROWS_PER_MOD):
    rows = range(r0i, min(n, r0i + ROWS_PER_MOD))
    s = HEADER
    for i in rows:
        for j in range(n):
            s += f'def E{i}_{j} : ℚ := {q1(E[(i, j)])}\n'
        s += f'def Erow{i} : List ℚ := [' + ', '.join(f'E{i}_{j}' for j in range(n)) + ']\n\n'
        for j in range(n):
            s += f'theorem pe{i}_{j} : pairOracle.pairOk Dn {i} {j} E{i}_{j} = true := by decide +kernel\n'
        proof = f'rowOk_nil Dn {i} {n} (by decide)'
        for j in reversed(range(n)):
            proof = f'rowOk_cons pe{i}_{j} ({proof})'
        s += f'\ntheorem rowOk{i} : rowOk Dn {i} 0 Erow{i} = true :=\n  {proof}\n\n'
    w(f'Energy/R{r0i:02d}.lean', s.replace('import CatalanCore.Uniform.Bank.Chi3.Env', 'import CatalanCore.Uniform.Bank.Chi3.Env\nimport CatalanCore.Uniform.Decay.PolyWire2.Energy2') + FOOT)
    emods.append(f'R{r0i:02d}')
s = 'import ' + '\nimport '.join(f'{NS}.Energy.{m}' for m in emods) + '\nimport CatalanCore.Uniform.Decay.PolyWire2.Energy2\n' + HEADER.split('\n', 1)[1]
s += 'def Etab : List (List ℚ) := [' + ', '.join(f'Erow{i}' for i in range(n)) + ']\n\n'
proof = f'tabOk_nil Dn {n} (by decide)'
for i in reversed(range(n)):
    proof = f'tabOk_cons rowOk{i} ({proof})'
s += f'theorem etab_ok : tabOk Dn 0 Etab = true :=\n  {proof}\n\n'
s += 'theorem etab_sum : tabSum Dn Etab ≤ Dn.Ibound := by decide +kernel\n'
w('Energy/Top.lean', s + FOOT)
print('emitted; Scap', float(Scap), 'Dt', float(Dt))
open(os.path.join(SCR, 'emit_summary.txt'), 'w').write(f'Esum {float(Esum)}\nG {float(G)}\nScap {float(Scap)} receipt {float(sc["Scap"])}\nDt {float(Dt)} receipt {float(sc["Dt"])}\n')
