from pathlib import Path
from fractions import Fraction as Q
import json,sys
R=Path(__file__).resolve().parents[4];S=R/'scripts/codex/bank/sevenths';D=json.loads((R.parents[1]/'outputs/Compatibility programme/bank-specs-2026-10-28/rank-sevenths.json').read_text());out=R/'CatalanCore/Uniform/Bank/Sevenths/RankMatch';out.mkdir(exist_ok=True);manifest=[]
def rat(q):q=Q(q);return f'({q.numerator} / {q.denominator} : ℚ)'
for case in D['cases']:
 for ci,c in enumerate(case['cells']):
  name=f'C{case["prime_class"]}S{ci:02}';vs=list(dict.fromkeys(tuple(pc['V']) for pc in c['price_pieces'] if isinstance(pc['V'],list)))
  if not vs:continue
  manifest.append('CatalanCore.Uniform.Bank.Sevenths.RankMatch.'+name)
  if sys.argv[1:] and name not in sys.argv[1:]:continue
  u,v=Q(c['left']),Q(c['right']);n=len(c['runs']);ps='''(a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)''';hs=f'''(hleft : {u.numerator} * r ≤ {u.denominator} * p)
    (hright : {v.denominator} * p ≤ {v.numerator} * r)''';args='a p r m s ha hp64 hp7 hrp hm1'
  text=f'''import CatalanCore.Uniform.Bank.Sevenths.RankCount.{name}
import CatalanCore.Uniform.Content.RankProducer.RationalMatches
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankMatch
open CatalanCore.Uniform.Content.RankProducer RankFibre RankData RankCount
open CatalanCore.Uniform.Content.RankProducer.Geometry
open scoped Classical
'''
  for vi,V in enumerate(vs):
   vn=f'{name}_V{vi}';text+=f'\ndef {vn} : ℚ × ℚ := ({rat(V[0])}, {rat(V[1])})\n';w={side:[sum(Q(z[0])*Q(V[1])-Q(z[1])*Q(V[0])==0 for z in case['types'][run['type_id']][side+'_loads']) for run in c['runs']] for side in ['row','column']};assert max(w['row']+w['column'])<=1
   def point(side):return ' + '.join(f'(if {name}_test{i} r p s x then 1 else 0)' for i in range(n) if w[side][i]) or '0'
   for side,fun in [('row','rationalRowMatches'),('column','rationalColMatches')]:
    tn=f'{name}_V{vi}_{side}';selected=[i for i in range(n) if w[side][i]];rhs=' + '.join(f'{name}_count{i} r p s' for i in selected) or '0'
    text+=f'''\ntheorem {tn}_pointwise {ps} {hs} (x : ZMod p) :
    {fun} ({name}_assignment {args} x) {vn} = {point(side)} := by
'''
    for i in range(n):
     text+=f'  by_cases h{i} : {name}_test{i} r p s x\n  · rw [{name}_assignment_on_run{i} {args} hleft hright x h{i}]\n'
     for j in range(i+1,n):text+=f'''    have hn{j} : ¬ {name}_test{j} r p s x := by
      intro hj
      rcases h{i} with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
'''
     simps=[f'if_neg h{j}' for j in range(i)]+[f'if_pos h{i}']+[f'if_neg hn{j}' for j in range(i+1,n)];text+='    simp only ['+', '.join(simps)+']\n    decide +kernel\n'
    text+='  simp only ['+name+'_assignment, '+', '.join(f'if_neg h{i}' for i in range(n))+']\n  rfl\n'
    text+=f'''\ntheorem {tn}_sum {ps} {hs} :
    (∑ x : ZMod p, {fun} ({name}_assignment {args} x) {vn}) = {rhs} := by
  calc
    _ = ∑ x : ZMod p, ({point(side)}) := Finset.sum_congr rfl (fun x _ =>
      {tn}_pointwise {args} hleft hright x)
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_boole, {', '.join(f'{name}_count{i}' for i in selected)}]
'''
   coeff=[sum(Q(run['count'][k])*(w['row'][i]+w['column'][i]) for i,run in enumerate(c['runs'])) for k in ['intercept','slope']]
   leading=f'({rat(coeff[0])} * (r : ℚ) + {rat(coeff[1])} * (p : ℚ))';selected=[i for i in range(n) if w['row'][i]+w['column'][i]]
   text+=f'''\ntheorem {name}_V{vi}_matched_lower {ps} {hs} :
    {leading} - (96 + 16 * ((r - s.card : ℕ) : ℚ)) ≤
      (((∑ x : ZMod p, rationalRowMatches ({name}_assignment {args} x) {vn}) +
        (∑ x : ZMod p, rationalColMatches ({name}_assignment {args} x) {vn}) : ℕ) : ℚ) := by
  rw [{name}_V{vi}_row_sum {args} hleft hright,
    {name}_V{vi}_column_sum {args} hleft hright]
  push_cast
  have hdepth : (0 : ℚ) ≤ ((r - s.card : ℕ) : ℚ) := Nat.cast_nonneg _
'''
   for i in selected:text+=f'  have h{i} := {name}_count_bounds{i} r p s hleft hright\n'
   text+='  linarith'+(' ['+', '.join(f'h{i}.1, h{i}.2' for i in selected)+']' if selected else '')+'\n';text+=f'\n#print axioms {name}_V{vi}_matched_lower\n'
  text+='end CatalanCore.Uniform.Bank.Sevenths.RankMatch\n';(out/(name+'.lean')).write_text(text,encoding='utf-8');print('Prepared selected line-count bridge',name,len(vs))
(S/'matches-manifest.json').write_text(json.dumps(manifest,indent=2),encoding='utf-8')
