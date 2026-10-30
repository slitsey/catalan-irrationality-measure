from pathlib import Path
from fractions import Fraction as Q
import json
R=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform');B=R/'CatalanCore/Uniform/Bank/Lambda/Prefix';B.mkdir(exist_ok=True)
a=Q(1,10);N=100;pcs=[]
for n in range(N-1,0,-1):
 u=a/(n+1);v=2*a/(2*n+1);w=a/n
 pcs.extend([(u,v,Q(23,10),Q(-n-1)),(v,w,Q(21,10),Q(n))])
def q(x):x=Q(x);return f'({x.numerator} / {x.denominator})'
masses=[]
for ci in range(6):
 ps=pcs[ci*33:(ci+1)*33];name=f'prefix{ci}';mass=sum((A*(v-u)+bb*(v*v-u*u)/2 for u,v,A,bb in ps),Q(0));masses.append(mass)
 rows=['  { s := '+q(u)+', t := '+q(v)+', α := '+q(A)+', β := '+q(bb)+', C := C0 }' for u,v,A,bb in ps]
 txt='''import CatalanCore.Uniform.Content.Member.Template
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore.Arith.Hybrid
'''
 txt+=f'noncomputable def {name} (C0 : ℝ) : List Piece := [\n'+',\n'.join(rows)+']\n'
 txt+=f'\ndef {name}Mass : ℚ := {q(mass)}\n'
 txt+=f'''theorem {name}_chain (C0 : ℝ) (hC : 0 ≤ C0) : Chain {q(ps[0][0])} ({name} C0) := by
  norm_num [{name}, Chain, hC]
theorem {name}_mass (C0 : ℝ) : listInt ({name} C0) = ({name}Mass : ℝ) := by
  norm_num [{name}, listInt, Piece.int, {name}Mass]
#print axioms {name}_chain
#print axioms {name}_mass
end CatalanCore.Uniform.Bank.Lambda
'''
 (B/f'P{ci}.lean').write_text(txt,encoding='utf-8')
prof=json.loads((R/'scripts/codex/bank/lambda/nouf-profile.json').read_text())
L=Q(11,5000)+sum(masses,Q(0))+sum((Q(c['mass']) for c in prof['classes']),Q(0))/2
D=Q(14627817894518751186053,3906250000000000000000);C=Q(1438085452130567,200000000000000)
assert C/(D-L)<Q(159693,5000)
txt='''import CatalanCore.Uniform.Bank.Lambda.Final
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
'''+f'def LamNoUFFinite : ℚ := {q(L)}\n'+'''theorem finite_Lam_lt_D : (LamNoUFFinite : ℝ) < (DL : ℝ) := by
  norm_num [LamNoUFFinite, DL]
theorem finite_noUF_X_le :
    (cL : ℝ) / ((DL : ℝ) - (LamNoUFFinite : ℝ)) ≤ ((159693 / 5000 : ℚ) : ℝ) := by
  norm_num [LamNoUFFinite, DL, cL]
#print axioms finite_Lam_lt_D
#print axioms finite_noUF_X_le
end CatalanCore.Uniform.Bank.Lambda
'''
(R/'CatalanCore/Uniform/Bank/Lambda/FiniteRate.lean').write_text(txt,encoding='utf-8')
(R/'scripts/codex/bank/lambda/finite-prefix.json').write_text(json.dumps(dict(N=N,pieces=len(pcs),prefix_mass=str(Q(11,5000)+sum(masses,Q(0))),lambda_finite=str(L),mu_upper=str(C/(D-L)),safe_bound='159693/5000'),indent=2),encoding='utf-8')
print('Prepared 198 finite prefix pieces in six leaves; rational measure bound',float(C/(D-L)))
