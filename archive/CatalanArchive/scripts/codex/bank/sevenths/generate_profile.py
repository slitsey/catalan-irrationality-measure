"""Replay the full q7 layer minimum and emit its exact finite Lean profiles."""
from pathlib import Path
from fractions import Fraction as Q
import json
import sys

sys.dont_write_bytecode = True
ROOT = Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform')
P = ROOT.parents[1]/'outputs/Compatibility programme'
sys.path.insert(0, str(P/'hybrid-alpha-2026-10-27'))
import _paths
sys.path.insert(0, str(P/'q4-mechanisms-uniform-2026-10-27'))
import newprice as N
import m3

al = Q(1, 12)
left, right, hi3 = 2*al, Q(49, 6), 1+4*al
rd = json.loads((P/'bank-specs-2026-10-28/rank-sevenths.json').read_text())
ud = json.loads((P/'bank-specs-2026-10-28/uf-sevenths.json').read_text())
results = []
for case, ucase in zip(rd['cases'], ud['cases']):
    assert case['root_index'] == ucase['root_index']
    ka = Q(case['pole_cut'])
    rank = [(Q(v['left']), Q(v['right']), N.Line(Q(v['line'][0]), Q(v['line'][1])))
            for c in case['cells'] for v in c['price_pieces']]
    uf = [(Q(v['left']), Q(v['right']), N.Line(Q(v['line']['intercept']), Q(v['line']['slope'])))
          for c in ucase['cells'] for v in c['price_pieces']]
    cuts = {al, left, right, hi3}
    cuts |= {x for x in N.breakpoints(al, ka) if left < x < right}
    cuts |= {x for x in N.g_kinks(al, ka) if left < x < right}
    cuts |= {x for u, v, f in rank+uf for x in (u, v)}
    fine = set(cuts)
    for u, v in zip(sorted(cuts), sorted(cuts)[1:]):
        if u < hi3:
            fine |= m3.kinks(al, ka, u, min(v, hi3))
    fine = sorted(x for x in fine if al <= x <= right)
    pieces = []
    for u, v in zip(fine, fine[1:]):
        mid = (u+v)/2
        T = N.Line(2+3*al, Q(-1)) if mid < left else N.trop_line(u, v, al, ka)
        ls = [('T', T)]
        if mid >= left:
            ls += [('R', next(f for a, b, f in rank if a < mid < b)),
                   ('UF', next(f for a, b, f in uf if a < mid < b))]
            g = N.g_line(mid, al, ka)
            if 1 < mid and ka*mid < 1 and (1+ka)*mid < 1+2*al:
                g = N.Line(Q(0), Q(0))
            ls.append(('strictLP', N.Line(T.intercept-g.intercept, T.slope-g.slope)))
        if mid < hi3:
            ls.extend(('M3D', f) for f in m3.P3_lines(al, ka, u, v))
        sub = {u, v}
        for _, f in ls:
            for _, g in ls:
                if f.slope != g.slope:
                    x = (g.intercept-f.intercept)/(f.slope-g.slope)
                    if u < x < v:
                        sub.add(x)
        for a, b in zip(sorted(sub), sorted(sub)[1:]):
            tag, f = min(ls, key=lambda tf: tf[1]((a+b)/2))
            assert f(a) >= 0 and f(b) >= 0
            line = [str(f.intercept), str(f.slope)]
            if pieces and pieces[-1]['line'] == line and pieces[-1]['layer'] == tag:
                pieces[-1]['right'] = str(b)
            else:
                pieces.append(dict(left=str(a), right=str(b), line=line, layer=tag))
    mass = sum((Q(v['line'][0])*(Q(v['right'])-Q(v['left']))+
                Q(v['line'][1])*(Q(v['right'])**2-Q(v['left'])**2)/2 for v in pieces), Q(0))
    results.append(dict(root=case['root_index'], pieces=pieces, mass=str(mass)))
prefix = 2*al+al**2/2
A = prefix+sum((Q(c['mass']) for c in results), Q(0))/6
assert A == Q(json.loads((P/'bank-specs-2026-10-28/replay-sevenths.json').read_text())['UF']['rational'])
out = dict(prefix_rational=str(prefix), prefix_log2=str(2*al**2), lambda_rational=str(A),
           classes=results, lean_supplier_proved=False)
(Path(__file__).parent/'profile.json').write_text(json.dumps(out, indent=2)+'\n')
print('Full strict profile reproduced exactly:', [len(c['pieces']) for c in results])

def rat(x):
    x = Q(x)
    return f'({x.numerator} / {x.denominator})'

dest = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT/'CatalanCore/Uniform/Bank/Sevenths/Profile'
dest.mkdir(parents=True, exist_ok=True)
imports = []
for c in results:
    name = 'profile'+str(c['root'])
    rows = [f'  {{ s := {rat(p["left"])}, t := {rat(p["right"])}, α := {rat(p["line"][0])}, β := {rat(p["line"][1])}, C := C0 }}' for p in c['pieces']]
    text = '''import CatalanCore.Uniform.Content.Member.Template
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore.Arith.Hybrid
'''
    text += f'/-- Full strict T/R/UF/LP/M3D envelope for root {c["root"]}. -/\nnoncomputable def {name} (C0 : ℝ) : List Piece := [\n'+',\n'.join(rows)+']\n'
    text += f'\ndef {name}Mass : ℚ := {rat(c["mass"])}\n'
    text += f'''theorem {name}_chain (C0 : ℝ) (hC : 0 ≤ C0) : Chain (1 / 12) ({name} C0) := by
  norm_num [{name}, Chain, hC]
theorem {name}_mass (C0 : ℝ) : listInt ({name} C0) = ({name}Mass : ℝ) := by
  norm_num [{name}, listInt, Piece.int, {name}Mass]
#print axioms {name}_chain
#print axioms {name}_mass
end CatalanCore.Uniform.Bank.Sevenths
'''
    (dest/f'C{c["root"]}.lean').write_text(text, encoding='utf-8')
    imports.append(f'CatalanCore.Uniform.Bank.Sevenths.Profile.C{c["root"]}')
text = '\n'.join('import '+i for i in imports)+'''
import CatalanCore.Uniform.Bank.Sevenths.Final
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore.Arith.Hybrid
/-- Exact integrated profile mass. Physical coverage remains a separate obligation. -/
theorem sevenths_profile_mass (C0 : ℝ) :
    49 / 288 + (1 / 72) * Real.log 2 +
      (listInt (profile1 C0) + listInt (profile2 C0) + listInt (profile3 C0) +
       listInt (profile4 C0) + listInt (profile5 C0) + listInt (profile6 C0)) / 6 = Lam7 := by
  rw [profile1_mass, profile2_mass, profile3_mass, profile4_mass, profile5_mass, profile6_mass]
  unfold profile1Mass profile2Mass profile3Mass profile4Mass profile5Mass profile6Mass Lam7
  push_cast
  ring
#print axioms sevenths_profile_mass
end CatalanCore.Uniform.Bank.Sevenths
'''
(dest/'Mass.lean').write_text(text, encoding='utf-8')
