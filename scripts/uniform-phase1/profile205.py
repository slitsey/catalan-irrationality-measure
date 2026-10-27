"""Independent exact integration of the frozen D58 205-cell leading profile.
This qualifies profile arithmetic only; physical content is a separate Lean theorem.
"""
from pathlib import Path
from fractions import Fraction as Q
import json, hashlib
P=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea')
S=P/'outputs/Compatibility programme/thin-windows-2026-10-24/complete31/final-audit-2026-10-26/final-audit-result.json'
O=P/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/bank'
W=P/'work/catalan-uniform/CatalanMeasure/GenD/Uniform/Bank'
O.mkdir(parents=True,exist_ok=True); W.mkdir(parents=True,exist_ok=True)
a=json.loads(S.read_text()); assert a['status']=='PASS' and len(a['rows'])==205
lines=['module','public import Mathlib.Data.Rat.Defs','public import CatalanMeasure.CellCert.RawInts','@[expose] public section','set_option Elab.async false','set_option profiler true','namespace CatalanMeasure.GenD.Uniform.Bank.Profile205','/-! Frozen exact leading-profile arithmetic. Physical source transport and content\nare supplied separately; these arithmetic checks alone assert no nullity bound. -/','def pieceIntegral (l r c s : Rat) : Rat := c*(r-l)+s*(r*r-l*l)/2']
def rat(q):
 q=Q(q); return f'({q.numerator} / {q.denominator} : Rat)'
last=Q(2); total=Q(0); receipts=[]; vals=[]
for i,row in enumerate(a['rows']):
 l,r=map(Q,row['interval']); assert l==last and l<r; pos=l; val=Q(0)
 terms=[]
 for pc in row['pieces']:
  u,v=map(Q,pc['interval']); c=Q(pc['line']['intercept']); s=Q(pc['line']['slope'])
  assert u==pos and u<v and v<=r
  z=c*(v-u)+s*(v*v-u*u)/2; assert z==Q(pc['integral']); val+=z; pos=v
  terms.append('pieceIntegral '+' '.join(map(rat,(u,v,c,s))))
 assert pos==r and val==Q(row['exact_integral']); last=r; total+=val; vals.append(val)
 lines += [f'def cell{i:03} : Rat := '+ ' + '.join(terms),f'theorem cell{i:03}_check : cell{i:03}={rat(val)} := by decide +kernel']
 receipts.append({'leaf':row['leaf_id'],'interval':row['interval'],'pieces':len(terms),'integral':str(val)})
assert last==Q(53,2) and total==Q(a['exact_audited_sum'])
lines += ['def integratedProfile : Rat := '+ ' + '.join(f'cell{i:03}' for i in range(205)),f'theorem integratedProfile_exact : integratedProfile={rat(total)} := by\n  simp only [integratedProfile, '+', '.join(f'cell{i:03}_check' for i in range(205))+']\n  decide +kernel', 'theorem integratedProfile_target : (2191363/100000 : Rat) < integratedProfile := by\n  rw [integratedProfile_exact]\n  decide +kernel','#print axioms integratedProfile_exact','end CatalanMeasure.GenD.Uniform.Bank.Profile205']
(W/'Profile205.lean').write_text('\n\n'.join(lines)+'\n',encoding='utf-8')
r={'status':'PASS independent Fraction integration, arithmetic layer only','count':205,'pieces':sum(x['pieces'] for x in receipts),'exact_integral':str(total),'source':str(S),'sha256':hashlib.sha256(S.read_bytes()).hexdigest(),'rows':receipts}
(O/'profile205-mirror.json').write_text(json.dumps(r,indent=2)+'\n')
print({k:v for k,v in r.items() if k!='rows'})
