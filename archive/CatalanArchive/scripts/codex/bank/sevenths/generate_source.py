from pathlib import Path
from fractions import Fraction as Q
from math import lcm
import json
R=Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\work\catalan-uniform')
P=R.parents[1]/'outputs/Compatibility programme/bank-specs-2026-10-28/rank-sevenths.json'
d=json.loads(P.read_text());out=R/'CatalanCore/Uniform/Bank/Sevenths/RankSource';out.mkdir(exist_ok=True)
manifest=[]
def line(v):
 a,b=Q(v['intercept']),Q(v['slope']);D=lcm(a.denominator,b.denominator)
 return int(a*D),int(b*D),D
for case in d['cases']:
 tnames={t:f'C{case["prime_class"]}T{k:02}' for k,t in enumerate(case['types'])}
 for ci,cell in enumerate(case['cells']):
  name=f'C{case["prime_class"]}S{ci:02}';names=sorted(set(tnames[v['type_id']] for v in cell['runs']))
  txt='import CatalanCore.Uniform.Bank.Sevenths.DigitShape\n'
  txt+='set_option Elab.async false\nset_option maxRecDepth 10000\nset_option maxHeartbeats 1600000\nnamespace CatalanCore.Uniform.Bank.Sevenths.RankSource\nopen CatalanCore.Uniform.Content.RankProducer.Geometry\n'
  u,v=Q(cell['left']),Q(cell['right'])
  for ri,run in enumerate(cell['runs']):
   typ=case['types'][run['type_id']];tn=tnames[run['type_id']];A,B,D=line(run['lower']);AA,BB,DD=line(run['upper']);j=case['root_index'];z=typ['pole_bit'];res=run['residue']
   head=f''' (r m p x : ℕ) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = {res}) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : {u.numerator} * r ≤ {u.denominator} * p)
    (hright : {v.denominator} * p ≤ {v.numerator} * r)
    (hlo : ({D} : ℤ) * x ≥ ({A} : ℤ) * r + ({B} : ℤ) * p + {4*D})
    (hhi : ({DD} : ℤ) * x ≤ ({AA} : ℤ) * r + ({BB} : ℤ) * p - {4*DD})'''
   for pred,field in [('rowDigit','R'),('colDigit','C')]:
    ns=[x['digit'] for x in typ['rows' if field=='R' else 'columns']]
    setname=f'{name}_run{ri}_{field}set'
    literal='{'+', '.join(map(str,ns))+'}' if ns else '∅'
    txt+=f'\ndef {setname} : Finset ℕ := {literal}\n'
    txt+=f'\ntheorem {name}_run{ri}_{field}'+head+f''' :
    ∀ d : ℕ, {pred} r m p x d ↔ d ∈ {setname} := by
  intro d
  constructor
  · intro h
    have hd := {pred}_lt_seven hm1 hrp hx h
    interval_cases d <;> norm_num [{pred}, {setname}] at * <;> omega
  · intro h
    have hd : d < 7 := by norm_num [{setname}] at h; omega
    interval_cases d <;> norm_num [{pred}, {setname}] at * <;> omega
'''
   txt+=f'\ntheorem {name}_run{ri}_bit'+head+f'''
    (a k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : 7 * k + a = {j} * p) :
    (if k < x then 1 else 0) = {z} := by
  split_ifs <;> omega
'''
  txt+='end CatalanCore.Uniform.Bank.Sevenths.RankSource\n'
  (out/(name+'.lean')).write_text(txt,encoding='utf-8');manifest.append('CatalanCore.Uniform.Bank.Sevenths.RankSource.'+name)
(R/'scripts/codex/bank/sevenths/source-manifest.json').write_text(json.dumps(manifest,indent=2),encoding='utf-8')
print('Prepared',len(manifest),'source-cell modules for 316 physical residue runs')
