from pathlib import Path
from fractions import Fraction as Q
import json,sys,re
R=Path(__file__).resolve().parents[4];S=R/'scripts/codex/bank/sevenths';D=json.loads((R.parents[1]/'outputs/Compatibility programme/bank-specs-2026-10-28/rank-sevenths.json').read_text());out=R/'CatalanCore/Uniform/Bank/Sevenths/RankFacts';out.mkdir(exist_ok=True);manifest=[]
def rat(q):q=Q(q);return f'({q.numerator} / {q.denominator} : ℚ)'
for case in D['cases']:
 names={t:f'C{case["prime_class"]}T{k:02}' for k,t in enumerate(case['types'])}
 for ci,c in enumerate(case['cells']):
  name=f'C{case["prime_class"]}S{ci:02}';manifest.append('CatalanCore.Uniform.Bank.Sevenths.RankFacts.'+name)
  if sys.argv[1:] and name not in sys.argv[1:]:continue
  used=sorted({run['type_id'] for run in c['runs']},key=lambda t:names[t]);text='import CatalanCore.Uniform.Bank.Sevenths.RankFibre.'+name+'\n'+''.join('import CatalanCore.Uniform.Bank.Sevenths.RankLoads.'+names[t]+'\n' for t in used)
  text+='''set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankFacts
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
open RankFibre RankData RankLoads
open CatalanCore.Uniform.Content.RankProducer.Geometry
open scoped Classical
'''
  text+=f'''\ntheorem {name}_load_facts (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6) (hp : rankPrimeCutoff < p) (x : ZMod p) :
    let c := {name}_assignment a p r m s ha hp64 hp7 hrp hm1 x
    (c.kr.card ≤ 1 ∧ c.kc.card ≤ 1) ∧
    (∀ d ∈ c.kr, (c.rload d).1 ∈ S p ∧ (c.rload d).2 ∈ S p) ∧
    (∀ d ∈ c.kc, (c.cload d).1 ∈ S p ∧ (c.cload d).2 ∈ S p ∧ castV p (c.cload d) ≠ 0) := by
  dsimp only
  unfold {name}_assignment
  split_ifs
'''
  for run in c['runs']:
   t=case['types'][run['type_id']];tn=names[run['type_id']];text+=f'  · refine ⟨{tn}_small_kills, ?_, ?_⟩\n'
   for side,key,loads,kind in [('kr','rows','row_loads','rload'),('kc','columns','column_loads','cload')]:
    digits=[t[key][i]['digit'] for i in t['killed_rows' if side=='kr' else 'killed_columns']];assert len(digits)<=1
    if not digits:text+=f'''    · intro d hd
      have he : {tn}.{side} = ∅ := rfl
      simp [he] at hd
'''
    else:
     digit=digits[0];v=t[loads][0]
     text+=f'''    · intro d hd
      have he : {tn}.{side} = {{{digit}}} := rfl
      have hd' : d = {digit} := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
'''
     if side=='kc':text+=f'      have hn := ({tn}_reduced_loads_nonzero p hp).2 {digit} hd\n'
     text+=f'      rw [{tn}_{kind}_{digit}]\n'
     q1,q2=rat(v[0]),rat(v[1]);unit1=f'rank_rational_mem p {q1} hp (by decide +kernel)';unit2=f'rank_rational_mem p {q2} hp (by decide +kernel)'
     if side=='kr':text+=f'      exact ⟨{unit1}, {unit2}⟩\n'
     else:text+=f'      exact ⟨{unit1}, {unit2}, by simpa only [{tn}_{kind}_{digit}] using hn⟩\n'
  text+='  · simp [trivCert, FibreCert.triv]\n';text+=f'\n#print axioms {name}_load_facts\nend CatalanCore.Uniform.Bank.Sevenths.RankFacts\n';text=re.sub(r'^(import .*RankLoads\.C[0-9]+)T[0-9]+$',r'\1',text,flags=re.M);seen=set();text='\n'.join(x for x in text.splitlines() if not (x.startswith('import ') and (x in seen or seen.add(x))))+'\n';(out/(name+'.lean')).write_text(text,encoding='utf-8');print('Prepared actual assignment local-ring facts',name)
(S/'facts-manifest.json').write_text(json.dumps(manifest,indent=2),encoding='utf-8')
