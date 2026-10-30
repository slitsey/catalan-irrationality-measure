from pathlib import Path
from fractions import Fraction as Q
import json
r=Path(__file__).resolve().parents[4];s=r/'scripts/codex/bank/sevenths';d=json.loads((r.parents[1]/'outputs/Compatibility programme/bank-specs-2026-10-28/rank-sevenths.json').read_text());out=r/'CatalanCore/Uniform/Bank/Sevenths/RankLoads';out.mkdir(exist_ok=True);manifest=[]
def rat(x):
 x=Q(x);return f'({x.numerator} / {x.denominator})'
for case in d['cases']:
 for k,t in enumerate(case['types'].values()):
  name=f'C{case["prime_class"]}T{k:02}'
  text=f'''import CatalanCore.Uniform.Bank.Sevenths.RankPalette.{name}
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem {name}_small_kills : {name}.kr.card ≤ 1 ∧ {name}.kc.card ≤ 1 := by decide +kernel

theorem {name}_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    {name}.Integral p := by
  apply {name}_integral p
  intro hd
  have hpos : 0 < {name}_den := by decide +kernel
  have hbound : {name}_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem {name}_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ {name}.kr, castV p ({name}.rload d) ≠ 0) ∧
    (∀ d ∈ {name}.kc, castV p ({name}.cload d) ≠ 0) := by
  constructor
'''
  for side,key,loadkey,kind in [('kr','rows','row_loads','rload'),('kc','columns','column_loads','cload')]:
   digits=[t[key][i]['digit'] for i in t['killed_rows' if side=='kr' else 'killed_columns']];assert len(digits)<=1
   if not digits:text+=f'''  · intro d hd
    have he : {name}.{side} = ∅ := rfl
    simp [he] at hd
'''
   else:
    digit=digits[0];v=t[loadkey][0];coord=0 if Q(v[0]) else 1;assert Q(v[coord]);fn='fst' if coord==0 else 'snd';vv=f'({rat(v[0])}, {rat(v[1])})'
    text+=f'''  · intro d hd
    have he : {name}.{side} = {{{digit}}} := rfl
    have hde : d = {digit} := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [{name}_{kind}_{digit}]
    exact rank_castV_ne_zero_of_{fn} p {vv} hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
'''
  text+=f'\n#print axioms {name}_large_integral\n#print axioms {name}_reduced_loads_nonzero\nend CatalanCore.Uniform.Bank.Sevenths.RankLoads\n';(out/(name+'.lean')).write_text(text,encoding='utf-8');manifest.append('CatalanCore.Uniform.Bank.Sevenths.RankLoads.'+name)
(s/'loads-manifest.json').write_text(json.dumps(manifest,indent=2),encoding='utf-8');print('Prepared',len(manifest),'actual reduced-load modules')

# Compile a full root class together; preserve each independent certificate declaration.
import re
archive=r/'archive/CatalanArchive/CatalanCore/Uniform/Bank/Sevenths/RankLoads'
archive.mkdir(parents=True,exist_ok=True)
groups=[]
for case in d['cases']:
 pc=case['prime_class'];blocks=[]
 for k,t in enumerate(case['types'].values()):
  p=out/f'C{pc}T{k:02}.lean';text=p.read_text(encoding='utf-8')
  blocks.append(text[text.index('theorem '):text.rindex('end CatalanCore.Uniform.Bank.Sevenths.RankLoads')])
  p.replace(archive/p.name)
 header=f"""import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C{pc}
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData
"""
 (out/f'C{pc}.lean').write_text(header+'\n'.join(blocks)+'\nend CatalanCore.Uniform.Bank.Sevenths.RankLoads\n',encoding='utf-8')
 groups.append('CatalanCore.Uniform.Bank.Sevenths.RankLoads.C'+str(pc))
(s/'loads-manifest.json').write_text(json.dumps(groups,indent=2),encoding='utf-8')
