from pathlib import Path
from fractions import Fraction as Q
from math import lcm
import json
R=Path(__file__).resolve().parents[4]
P=R.parents[1]/'outputs/Compatibility programme/bank-specs-2026-10-28/rank-sevenths.json'
d=json.loads(P.read_text(encoding='utf-8'))
out=R/'CatalanCore/Uniform/Bank/Sevenths/RankFibre';out.mkdir(exist_ok=True)
manifest=[]
def line(v):
 a,b=Q(v['intercept']),Q(v['slope']);D=lcm(a.denominator,b.denominator)
 return int(a*D),int(b*D),D
exec(Path(__file__).with_name('fibre_assignment.py').read_text(encoding='utf-8-sig'))
for case in d['cases']:
 tnames={t:f'C{case["prime_class"]}T{k:02}' for k,t in enumerate(case['types'])}
 for ci,cell in enumerate(case['cells']):
  name=f'C{case["prime_class"]}S{ci:02}'
  names=[f'C{case["prime_class"]}']
  txt='import CatalanCore.Uniform.Bank.Sevenths.CommonMinorRealize\nimport CatalanCore.Uniform.Content.RankProducer.Boundary\nimport CatalanCore.Uniform.Bank.Sevenths.Band\n'
  txt+=f'import CatalanCore.Uniform.Bank.Sevenths.RankSource.{name}\n'
  txt+=''.join(f'import CatalanCore.Uniform.Bank.Sevenths.RankPalette.{n}\n' for n in names)
  txt+='set_option Elab.async false\nnamespace CatalanCore.Uniform.Bank.Sevenths.RankFibre\n'
  txt+='open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.RankProducer\n'
  txt+='open CatalanCore.Uniform.Content.RankProducer.Geometry RankSource RankData\nopen scoped Classical\n'
  u,v=Q(cell['left']),Q(cell['right'])
  for ri,run in enumerate(cell['runs']):
   typ=case['types'][run['type_id']];tn=tnames[run['type_id']]
   A,B,D=line(run['lower']);AA,BB,DD=line(run['upper']);j=case['root_index'];z=typ['pole_bit'];res=run['residue']
   txt+=f"""
theorem {name}_run{ri} (a p Bnd : ℕ) [Fact p.Prime] (hp7 : ¬ p ∣ 7)
    (hc : ∀ j, (D7Frame a).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (D7Frame a).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (D7Frame a).q j * Bnd + (D7Frame a).u j ≤ p ^ 2)
    (r m x : ℕ) (s : Finset (Fin r)) (hr : r % 2 = 0) (hp : p % 2 = 1)
    (hxpar : x % 2 = {res}) (hx : 4 ≤ x) (hxp : x < p)
    (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6) (hrp : r ≤ 6 * p)
    (hleft : {u.numerator} * r ≤ {u.denominator} * p)
    (hright : {v.denominator} * p ≤ {v.numerator} * r)
    (hlo : ({D} : ℤ) * x ≥ ({A} : ℤ) * r + ({B} : ℤ) * p + {4*D})
    (hhi : ({DD} : ℤ) * x ≤ ({AA} : ℤ) * r + ({BB} : ℤ) * p - {4*DD})
    (k : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hk : k < p) (hroot : 7 * k + a = {j} * p)
    (hgood : x ∉ deletedResidues r p s) (hden : ¬ p ∣ {tn}_den) :
    {tn}.Ok ∧ {tn}.Integral p ∧
      Realizes ((D7Frame a).poleSplit Bnd hc hpq hp3 hbd)
        (rowsOf r m s) (colsOf r m s) (x : ZMod p) {tn} := by
  refine ⟨{tn}_ok, {tn}_integral p hden, ?_⟩
  apply realizes_commonMinor_D7Frame a p Bnd hp7 hc hpq hp3 hbd r m s k {j} x {z}
    hk (by omega) hxp
    ({name}_run{ri}_bit r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi a k ha hroot)
    {tn}
  · exact {name}_run{ri}_R r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact {name}_run{ri}_C r m p x hr hp hxpar hx hxp hm1 hm2 hrp hleft hright hlo hhi
  · exact kept_of_not_deleted r p s x hxp hgood
  · exact {tn}_palette.1
  · exact fun d hd => ({tn}_palette.2 d hd).1
"""
  txt+=assignment(case,cell,name,tnames)
  txt+=f'\n#print axioms {name}_run0\nend CatalanCore.Uniform.Bank.Sevenths.RankFibre\n'
  (out/(name+'.lean')).write_text(txt,encoding='utf-8')
  manifest.append('CatalanCore.Uniform.Bank.Sevenths.RankFibre.'+name)
(R/'scripts/codex/bank/sevenths/fibre-manifest.json').write_text(json.dumps(manifest,indent=2),encoding='utf-8')
print('Prepared',len(manifest),'physical source-to-certificate consumers')
