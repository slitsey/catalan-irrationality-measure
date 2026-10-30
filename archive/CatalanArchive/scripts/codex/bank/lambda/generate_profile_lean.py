from pathlib import Path
from fractions import Fraction as Q
import json
R=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform');S=R/'scripts/codex/bank/lambda';B=R/'CatalanCore/Uniform/Bank/Lambda/Profile';B.mkdir(exist_ok=True)
d=json.loads((S/'nouf-profile.json').read_text())
def q(x):
 x=Q(x);return f'({x.numerator} / {x.denominator})'
for c in d['classes']:
 n=c['root'];name=f'profile{n}';rows=[]
 for p in c['pieces']:
  rows.append('  { s := '+q(p['left'])+', t := '+q(p['right'])+', α := '+q(p['line'][0])+', β := '+q(p['line'][1])+', C := C0 }')
 txt='''import CatalanCore.Uniform.Content.Member.Template
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore.Arith.Hybrid
'''
 txt+=f'/-- The no-UF affine envelope for root {n}; C0 is the fixed per-prime debit. -/\nnoncomputable def {name} (C0 : ℝ) : List Piece := [\n'+',\n'.join(rows)+']\n'
 txt+=f'\ndef {name}Mass : ℚ := {q(c["mass"])}\n'
 txt+=f'''theorem {name}_chain (C0 : ℝ) (hC : 0 ≤ C0) : Chain (1 / 10) ({name} C0) := by
  norm_num [{name}, Chain, hC]
theorem {name}_mass (C0 : ℝ) : listInt ({name} C0) = ({name}Mass : ℝ) := by
  norm_num [{name}, listInt, Piece.int, {name}Mass]
#print axioms {name}_chain
#print axioms {name}_mass
end CatalanCore.Uniform.Bank.Lambda
'''
 (B/f'C{n}.lean').write_text(txt,encoding='utf-8')
txt='''import CatalanCore.Uniform.Bank.Lambda.Profile.C1
import CatalanCore.Uniform.Bank.Lambda.Profile.C3
import CatalanCore.Uniform.Bank.Lambda.NoUF
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore.Arith.Hybrid
/-- The infinite sawtooth prefix (0,1/10) plus the two finite class envelopes.
This identifies the mass; physical price coverage is a separate obligation. -/
theorem noUF_profile_mass (C0 : ℝ) :
    41 / 200 + (1 / 50) * Real.log 2 +
      (listInt (profile1 C0) + listInt (profile3 C0)) / 2 = LamNoUF := by
  rw [profile1_mass, profile3_mass]
  unfold profile1Mass profile3Mass LamNoUF
  push_cast
  ring
#print axioms noUF_profile_mass
end CatalanCore.Uniform.Bank.Lambda
'''
(B/'Mass.lean').write_text(txt,encoding='utf-8')
print('Prepared the two exact finite profiles and no-UF mass identity')
