from pathlib import Path
from fractions import Fraction as Q
from math import lcm
import hashlib,json,re
R=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform')
B=R/'CatalanCore/Uniform/Bank/Lambda'
S=R/'scripts/codex/bank/lambda'
P=R.parents[1]/'outputs/Compatibility programme/bank-specs-2026-10-28'

def put(n,s):
 p=B/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s,encoding='utf-8')

def rat(x):
 x=Q(x)
 return f'({x.numerator} / {x.denominator})' if x.denominator!=1 else (f'({x.numerator})' if x<0 else str(x.numerator))
def fs(xs):return '{'+', '.join(map(str,xs))+'}' if xs else '∅'
def vec(xs):
 return 'fun d => match d with '+ ' '.join(f'| {d} => {rat(v)}' for d,v in sorted(xs.items()))+' | _ => 0' if xs else 'fun _ => 0'
def mat(A,rs,cs):
 vals=[(r,c,v) for r,row in zip(rs,A) for c,v in zip(cs,row) if Q(v)]
 return 'fun d e => match d, e with '+' '.join(f'| {r}, {c} => {rat(v)}' for r,c,v in vals)+' | _, _ => 0' if vals else 'fun _ _ => 0'

data=json.loads((P/'rank-lambda.json').read_text())
manifest=[]
for case in data['cases']:
 for k,(tid,t) in enumerate(case['types'].items()):
  name=f'C{case["prime_class"]}T{k:02}'
  rs=[x['digit'] for x in t['rows']];cs=[x['digit'] for x in t['columns']]
  lf={};ee={}
  for x in t['rows']+t['columns']:
   d=x['digit']
   if d in lf:assert Q(lf[d])==Q(x['L']) and Q(ee[d])==Q(x['E'])
   lf[d]=x['L'];ee[d]=x['E']
  den=lcm(*(Q(v).denominator for key in ('L','Linv','P','Pinv') for row in t[key] for v in row))
  kr=[rs[x] for x in t['killed_rows']];kc=[cs[x] for x in t['killed_columns']]
  txt='''import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
'''
  txt+=f'/-- Source type {tid}, root class {case["prime_class"]}. -/\ndef {name} : FibreCert where\n'
  for key,value in [('R',fs(rs)),('C',fs(cs)),('lf',vec(lf)),('ee',vec(ee)),('Lq',mat(t['L'],rs,rs)),("Lq'",mat(t['Linv'],rs,rs)),('Pq',mat(t['P'],cs,cs)),("Pq'",mat(t['Pinv'],cs,cs)),('kr',fs(kr)),('kc',fs(kc))]:txt+=f'  {key} := {value}\n'
  txt+=f'\ntheorem {name}_ok : {name}.Ok := by\n  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel\n'
  txt+=f'\ndef {name}_den : ℕ := {den}\n'
  txt+=f'''theorem {name}_den_ok :
    (∀ d ∈ {name}.R, ∀ e ∈ {name}.R, ({name}.Lq d e).den ∣ {name}_den ∧ ({name}.Lq' d e).den ∣ {name}_den) ∧
    (∀ d ∈ {name}.C, ∀ e ∈ {name}.C, ({name}.Pq d e).den ∣ {name}_den ∧ ({name}.Pq' d e).den ∣ {name}_den) := by
  constructor <;> decide +kernel
'''
  for typ,digits,loads in [('rload',kr,t['row_loads']),('cload',kc,t['column_loads'])]:
   for d,v in zip(digits,loads):
    txt+=f'theorem {name}_{typ}_{d} : {name}.{typ} {d} = ({rat(v[0])}, {rat(v[1])}) := by decide +kernel\n'
  txt+=f'#print axioms {name}_ok\n#print axioms {name}_den_ok\nend CatalanCore.Uniform.Bank.Lambda.RankData\n'
  put(f'RankData/{name}.lean',txt)
  manifest.append(dict(module=f'CatalanCore.Uniform.Bank.Lambda.RankData.{name}',type_id=tid,prime_class=case['prime_class'],name=name))
(S/'rank-manifest.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256((P/'rank-lambda.json').read_bytes()).hexdigest(),certificates=manifest),indent=2),encoding='utf-8')
put('RankData/Audit.lean','\n'.join('import '+m['module'] for m in manifest)+'\n')

text=(B/'Final.lean').read_text()
text=text.replace('import CatalanCore.Uniform.Bank.Lambda.NV','import CatalanCore.Uniform.Bank.Lambda.Final')
text=text.replace('25845089911312474748789','25867615342809042650399').replace('LamL','LamNoUF').replace('lambda_X_le','lambda_noUF_X_le').replace('lambda_measure','lambda_noUF_measure').replace('315113 / 10000','159693 / 5000')
text=re.sub(r'def DL : ℚ :=[^\n]*\n','',text)
text=re.sub(r'def cL : ℚ :=[^\n]*\n','',text)
put('NoUF.lean',text)
text=(B/'Members.lean').read_text().replace('.Lambda.Final','.Lambda.NoUF').replace('lambda_measure','lambda_noUF_measure').replace('LamL','LamNoUF').replace('315113 / 10000','159693 / 5000')
put('NoUFMembers.lean',text)
text=(B/'Content.lean').read_text().replace('lambda_content_of_pricing (Fr','lambda_content_of_pricing_at (Λ : ℝ) (Fr').replace('LamL','Λ')
put('ContentAt.lean',text)
print('Generated',len(manifest),'rank certificates and no-UF assembly')
