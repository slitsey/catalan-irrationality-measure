from pathlib import Path
from fractions import Fraction as Q
import json,sys
R=Path(__file__).resolve().parents[4];S=R/'scripts/codex/bank/lambda';D=json.loads((R.parents[1]/'outputs/Compatibility programme/bank-specs-2026-10-28/rank-lambda.json').read_text());out=R/'CatalanCore/Uniform/Bank/Lambda/RankPrice';out.mkdir(exist_ok=True);manifest=[]
def rat(q):
 q=Q(q);return f'({q.numerator} / {q.denominator} : ℚ)'
def affine(v):return f'({rat(v[0])} * (r : ℚ) + {rat(v[1])} * (p : ℚ))'
for case in D['cases']:
 names={t:f'C{case["prime_class"]}T{k:02}' for k,t in enumerate(case['types'])}
 for ci,c in enumerate(case['cells']):
  name=f'C{case["prime_class"]}S{ci:02}';manifest.append('CatalanCore.Uniform.Bank.Lambda.RankPrice.'+name)
  if sys.argv[1:] and name not in sys.argv[1:]:continue
  path=out/(name+'.lean');old=path.read_text(encoding='utf-8') if path.exists() else ''
  if f'theorem {name}_physical_valid' in old:continue
  u,z=Q(c['left']),Q(c['right']);cl=case['prime_class'];L=affine(c['balanced_kills']);E='(48 + 8 * ((r - s.card : ℕ) : ℚ))';depth='((r - s.card : ℕ) : ℚ)'
  ps='''(a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp : rankPrimeCutoff < p) (hr : r % 2 = 0)
    (hodd : p % 2 = 1) (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5)
    (hm2 : r ≤ 10 * m + 5)'''
  hs=f'''(hleft : {u.numerator} * r ≤ {u.denominator} * p)
    (hright : {z.denominator} * p ≤ {z.numerator} * r) (hclass : root4 a p = {cl})'''
  args='a p r m s ha hp29 hp4 hrp hm1';cert=f'{name}_assignment {args}'
  member='''RankMember (pipelineFrame a ha) (u4 a) q4 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p'''
  head=f'''import CatalanCore.Uniform.Bank.Lambda.RankCount.{name}
import CatalanCore.Uniform.Bank.Lambda.RankMatch.{name}
import CatalanCore.Uniform.Bank.Lambda.RankFacts.{name}
import CatalanCore.Uniform.Bank.Lambda.RankAffine
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankPrice
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
open CatalanCore.Uniform.Content.RankProducer
open CatalanCore.Uniform.Bank.Chi3Rank
open RankFibre RankData RankCount RankFacts RankMatch
open scoped Classical
'''
  dens=', '.join(names[t]+'_den' for t in sorted({x['type_id'] for x in c['runs']},key=lambda t:names[t]))
  body=f'''\ntheorem {name}_physical_valid {ps} {hs}
    (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4) (x : ZMod p) :
    ({cert} x).Ok ∧ ({cert} x).Integral p ∧
      Realizes (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1)
        (rowsOf r m s) (colsOf r m s) x ({cert} x) := by
  have hroot : 4 * pole4 a p + a = {cl} * p := by
    have h := (root4_spec a p ha hodd).2.1
    rw [hclass] at h
    simpa only [Nat.mul_one, Nat.one_mul, Nat.mul_comm] using h
  have hden : ∀ N ∈ ([{dens}] : List ℕ), ¬ p ∣ N := by
    intro N hN hd
    have hb : ∀ N ∈ ([{dens}] : List ℕ), 0 < N ∧ N ≤ rankPrimeCutoff := by decide +kernel
    have hle := Nat.le_of_dvd (hb N hN).1 hd
    have hbound := (hb N hN).2
    omega
  exact {name}_assignment_valid {args} hr hodd hm2 hleft hright
    (pole4 a p) (root4_spec a p ha hodd).2.2 hroot hden x
'''
  setup=f'''  have hp29 : 29 ≤ p := rankPrimeCutoff_ge_twentyNine.trans hp.le
  have hp4 : ¬ p ∣ 4 := by
    intro hd
    have hle := Nat.le_of_dvd (by norm_num : 0 < 4) hd
    omega
  let cert := {cert}
  have hdata := {name}_physical_valid a p r m s ha hp hr hodd hrp hm1 hm2 hleft hright hclass hp29 hp4
  have hOk : ∀ x, (cert x).Ok := fun x => (hdata x).1
  have hInt : ∀ x, (cert x).Integral p := fun x => (hdata x).2.1
  have hReal : ∀ x, Realizes (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x (cert x) := fun x => (hdata x).2.2
  have hR0 := {name}_row_bounds {args} hleft hright
  have hC0 := {name}_col_bounds {args} hleft hright
'''
  if not old:
   body+=f'''\ntheorem {name}_raw_member {ps} {hs} :
    ∃ M : {member},
      (M.price : ℚ) ≤ {affine(c['raw'])} + 49 + 8 * {depth} := by
{setup}  obtain ⟨M, hM⟩ := rank_raw_member {args} cert hOk hInt hReal {L} {E} hR0.1 hC0.1
  exact ⟨M, by linarith⟩
#print axioms {name}_raw_member
'''
  vs=list(dict.fromkeys(tuple(pc['V']) for pc in c['price_pieces'] if isinstance(pc['V'],list)))
  for vi,V in enumerate(vs):
   vn=f'{name}_V{vi}';match=[Q(0),Q(0)]
   for run in c['runs']:
    t=case['types'][run['type_id']];w=sum(Q(x[0])*Q(V[1])-Q(x[1])*Q(V[0])==0 for x in t['row_loads']+t['column_loads'])
    for k,key in enumerate(['intercept','slope']):match[k]+=w*Q(run['count'][key])
   line=[Q(11,5)-match[0],-match[1]];G=affine(match)
   body+=f'''\ntheorem {vn}_member {ps} {hs} :
    ∃ M : {member},
      (M.price : ℚ) ≤ {affine(line)} + 289 + 48 * {depth} := by
{setup}  have hdepth : (0 : ℚ) ≤ {depth} := Nat.cast_nonneg _
  have hR : {L} - {E} ≤ ((∑ x : ZMod p, (cert x).kr.card : ℕ) : ℚ) ∧
      ((∑ x : ZMod p, (cert x).kr.card : ℕ) : ℚ) ≤ {L} + {E} := by
    constructor <;> linarith [hR0.1, hR0.2]
  have hC : {L} - {E} ≤ ((∑ x : ZMod p, (cert x).kc.card : ℕ) : ℚ) ∧
      ((∑ x : ZMod p, (cert x).kc.card : ℕ) : ℚ) ≤ {L} + {E} := by
    constructor <;> linarith [hC0.1, hC0.2]
  have hf := {name}_load_facts {args} hp
  have hv1 : {vn}.1 ∈ S p := rank_rational_mem p {vn}.1 hp (by decide +kernel)
  have hv2 : {vn}.2 ∈ S p := rank_rational_mem p {vn}.2 hp (by decide +kernel)
  have hv : castV p {vn} ≠ 0 := rank_castV_ne_zero_of_fst p {vn} hp
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hm0 := {vn}_matched_lower {args} hleft hright
  have hMatch : {G} - 2 * {E} ≤
      (((∑ x : ZMod p, rationalRowMatches (cert x) {vn}) +
        (∑ x : ZMod p, rationalColMatches (cert x) {vn}) : ℕ) : ℚ) := by linarith
  obtain ⟨M, hM⟩ := rank_affine_member {args} cert hOk hInt hReal
    (fun x => (hf x).1.1) (fun x => (hf x).1.2) {vn} hv1 hv2 hv
    (fun x => (hf x).2.1) (fun x d hd => ⟨((hf x).2.2 d hd).1, ((hf x).2.2 d hd).2.1⟩)
    (fun x d hd => ((hf x).2.2 d hd).2.2) {L} {G} {E} hR hC hMatch
  exact ⟨M, by linarith⟩
#print axioms {vn}_member
'''
  if old:
   ending='end CatalanCore.Uniform.Bank.Lambda.RankPrice';assert old.rstrip().endswith(ending)
   extras='\n'.join(x for x in head.splitlines() if x.startswith('import '))+'\n'
   text=extras+old.rstrip()[:-len(ending)]+'open RankFacts RankMatch\n'+body+ending+'\n'
  else:text=head+body+'end CatalanCore.Uniform.Bank.Lambda.RankPrice\n'
  path.write_text(text,encoding='utf-8');print('Prepared physical member prices',name)
(S/'prices-manifest.json').write_text(json.dumps(manifest,indent=2),encoding='utf-8')