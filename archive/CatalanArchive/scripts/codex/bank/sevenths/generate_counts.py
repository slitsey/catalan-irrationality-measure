from pathlib import Path
from fractions import Fraction as Q
from math import lcm
import json,sys
R=Path(__file__).resolve().parents[4];S=R/'scripts/codex/bank/sevenths';D=json.loads((R.parents[1]/'outputs/Compatibility programme/bank-specs-2026-10-28/rank-sevenths.json').read_text());out=R/'CatalanCore/Uniform/Bank/Sevenths/RankCount';out.mkdir(exist_ok=True)
def rat(v):
 v=Q(v);return f'({v.numerator} / {v.denominator} : ℚ)'
def aff(v):return f'({rat(v["intercept"])} * (r : ℚ) + {rat(v["slope"])} * (p : ℚ))'
def line(v):
 a,b=Q(v['intercept']),Q(v['slope']);d=lcm(a.denominator,b.denominator);return int(a*d),int(b*d),d
manifest=[]
for case in D['cases']:
 names={t:f'C{case["prime_class"]}T{k:02}' for k,t in enumerate(case['types'])}
 for ci,c in enumerate(case['cells']):
  name=f'C{case["prime_class"]}S{ci:02}';manifest.append('CatalanCore.Uniform.Bank.Sevenths.RankCount.'+name)
  if sys.argv[1:] and name not in sys.argv[1:]:continue
  u,v=Q(c['left']),Q(c['right']);n=len(c['runs']);ps='''(a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6)''';hs=f'''(hleft : {u.numerator} * r ≤ {u.denominator} * p)
    (hright : {v.denominator} * p ≤ {v.numerator} * r)''';args='a p r m s ha hp64 hp7 hrp hm1';w={side:[len(case['types'][run['type_id']]['killed_rows' if side=='row' else 'killed_columns']) for run in c['runs']] for side in ['row','col']};assert max(w['row']+w['col'])<=1
  text=f'''import CatalanCore.Uniform.Bank.Sevenths.RankFibre.{name}
import CatalanCore.Uniform.Content.RankProducer.RunFibres
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankCount
open CatalanCore CatalanCore.Uniform.Content.RankProducer RankFibre RankData
open CatalanCore.Uniform.Content.RankProducer.Geometry
open scoped Classical
'''
  for i,run in enumerate(c['runs']):
   lo,hi=aff(run['lower']),aff(run['upper']);A,B,d=line(run['lower']);C,E,e=line(run['upper']);res=run['residue'];cs=f'{name}_count{i}'
   text+=f'''
noncomputable def {cs} (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) : ℕ :=
  ((Finset.univ : Finset (ZMod p)).filter ({name}_test{i} r p s)).card

theorem {name}_endpoints{i} (r p : ℕ) {hs} :
    0 ≤ {lo} ∧ {lo} ≤ {hi} ∧ {hi} ≤ (p : ℚ) := by
  have hL : ({u.numerator} : ℚ) * r ≤ ({u.denominator} : ℚ) * p := by exact_mod_cast hleft
  have hR : ({v.denominator} : ℚ) * p ≤ ({v.numerator} : ℚ) * r := by exact_mod_cast hright
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem {name}_good{i} (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) {hs} :
    goodRunFibres r p {res} s {lo} {hi} =
      ((Finset.univ : Finset (ZMod p)).filter ({name}_test{i} r p s)) := by
  have hlo0 := ({name}_endpoints{i} r p hleft hright).1
  ext x
  have hxp : x.val < p := ZMod.val_lt x
  simp only [goodRunFibres, runResidues, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_range, hxp, true_and, {name}_test{i}]
  constructor
  · rintro ⟨⟨hpar, hlo, hhi⟩, hgood⟩
    have hxQ : (4 : ℚ) ≤ x.val := by linarith
    have hLQ : ({A} : ℚ) * r + ({B} : ℚ) * p + {4*d} ≤ ({d} : ℚ) * x.val := by nlinarith [hlo]
    have hRQ : ({e} : ℚ) * x.val ≤ ({C} : ℚ) * r + ({E} : ℚ) * p - {4*e} := by nlinarith [hhi]
    exact ⟨hpar, by exact_mod_cast hxQ, by exact_mod_cast hLQ, by exact_mod_cast hRQ, hgood⟩
  · rintro ⟨hpar, hx, hlo, hhi, hgood⟩
    have hLQ : ({A} : ℚ) * r + ({B} : ℚ) * p + {4*d} ≤ ({d} : ℚ) * x.val := by exact_mod_cast hlo
    have hRQ : ({e} : ℚ) * x.val ≤ ({C} : ℚ) * r + ({E} : ℚ) * p - {4*e} := by exact_mod_cast hhi
    exact ⟨⟨hpar, by nlinarith [hLQ], by nlinarith [hRQ]⟩, hgood⟩

theorem {name}_count_bounds{i} (r p : ℕ) [Fact p.Prime] (s : Finset (Fin r)) {hs} :
    {aff(run['count'])} - 6 - ((r - s.card : ℕ) : ℚ) ≤ {cs} r p s ∧
      ({cs} r p s : ℚ) ≤ {aff(run['count'])} + 6 := by
  obtain ⟨hl, hle, hh⟩ := {name}_endpoints{i} r p hleft hright
  have h := goodRunFibres_card_bounds r p {res} s {lo} {hi} (by decide) hl hle hh
  rw [{name}_good{i} r p s hleft hright] at h
  change _ ≤ ({cs} r p s : ℚ) ∧ ({cs} r p s : ℚ) ≤ _ at h
  constructor <;> linarith [h.1, h.2]
'''
  def point(side):return ' + '.join(f'(if {name}_test{i} r p s x then 1 else 0)' for i in range(n) if w[side][i]) or '0'
  text+=f'''\ntheorem {name}_pointwise {ps} {hs} (x : ZMod p) :
    ({name}_assignment {args} x).kr.card = {point('row')} ∧
    ({name}_assignment {args} x).kc.card = {point('col')} := by
'''
  for i in range(n):
   text+=f'  by_cases h{i} : {name}_test{i} r p s x\n  · rw [{name}_assignment_on_run{i} {args} hleft hright x h{i}]\n'
   for j in range(i+1,n):text+=f'''    have hn{j} : ¬ {name}_test{j} r p s x := by
      intro hj
      rcases h{i} with ⟨hpar0, hx0, hlo0, hhi0, hg0⟩
      rcases hj with ⟨hpar1, hx1, hlo1, hhi1, hg1⟩
      omega
'''
   simpl=[f'if_neg h{j}' for j in range(i)]+[f'if_pos h{i}']+[f'if_neg hn{j}' for j in range(i+1,n)]
   text+='    simp only ['+', '.join(simpl)+']\n    constructor <;> decide +kernel\n'
  text+='  simp only ['+name+'_assignment, '+', '.join(f'if_neg h{i}' for i in range(n))+']\n  constructor <;> rfl\n'
  for side,field in [('row','kr'),('col','kc')]:
   selected=[i for i in range(n) if w[side][i]];rhs=' + '.join(f'{name}_count{i} r p s' for i in selected) or '0'
   text+=f'''\ntheorem {name}_{side}_sum {ps} {hs} :
    (∑ x : ZMod p, ({name}_assignment {args} x).{field}.card) = {rhs} := by
  calc
    _ = ∑ x : ZMod p, ({point(side)}) := Finset.sum_congr rfl (fun x _ =>
      ({name}_pointwise {args} hleft hright x).{'1' if side=='row' else '2'})
    _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_boole, {', '.join(f'{name}_count{i}' for i in selected)}]
'''
   ka,kb=c['balanced_kills'];leading=f'({rat(ka)} * (r : ℚ) + {rat(kb)} * (p : ℚ))'
   text+=f'''\ntheorem {name}_{side}_bounds {ps} {hs} :
    {leading} - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      ((∑ x : ZMod p, ({name}_assignment {args} x).{field}.card : ℕ) : ℚ) ∧
    ((∑ x : ZMod p, ({name}_assignment {args} x).{field}.card : ℕ) : ℚ) ≤ {leading} + 48 := by
  rw [{name}_{side}_sum {args} hleft hright]
  push_cast
  have hdepth : (0 : ℚ) ≤ ((r - s.card : ℕ) : ℚ) := Nat.cast_nonneg _
'''
   for i in selected:text+=f'  have h{i} := {name}_count_bounds{i} r p s hleft hright\n'
   text+='  constructor <;> linarith'+(' ['+', '.join(f'h{i}.1, h{i}.2' for i in selected)+']' if selected else '')+'\n'
  text+=f'\n#print axioms {name}_row_bounds\n#print axioms {name}_col_bounds\nend CatalanCore.Uniform.Bank.Sevenths.RankCount\n';(out/(name+'.lean')).write_text(text,encoding='utf-8');print('Prepared actual count assembly',name)
(S/'counts-manifest.json').write_text(json.dumps(manifest,indent=2),encoding='utf-8')
