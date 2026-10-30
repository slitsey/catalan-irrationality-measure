from pathlib import Path
from fractions import Fraction as Q
import json,sys
R=Path(__file__).resolve().parents[4];S=Path(__file__).parent
D=json.loads((R.parents[1]/'outputs/Compatibility programme/bank-specs-2026-10-28/rank-sevenths.json').read_text())
O=R/'CatalanCore/Uniform/Bank/Sevenths/RankPrice';O.mkdir(exist_ok=True)
def rat(x):x=Q(x);return f'({x.numerator} / {x.denominator} : ℚ)'
def aff(a,b):return f'({rat(a)} * (r : ℚ) + {rat(b)} * (p : ℚ))'
manifest=[]
for case in D['cases']:
 pc=case['prime_class'];root=case['root_index'];names={t:f'C{pc}T{k:02}' for k,t in enumerate(case['types'])}
 for ci,c in enumerate(case['cells']):
  name=f'C{pc}S{ci:02}';manifest.append('CatalanCore.Uniform.Bank.Sevenths.RankPrice.'+name)
  if sys.argv[1:] and name not in sys.argv[1:]:continue
  u,v=Q(c['left']),Q(c['right']);K1,K2=map(Q,c['balanced_kills']);vs=list(dict.fromkeys(tuple(x['V']) for x in c['price_pieces'] if isinstance(x['V'],list)))
  choices=[]
  for x in c['price_pieces']:
   A,B=map(Q,x['line']);raw=(A==Q(13,6)-K1 and B==-K2)
   vv=None if raw else tuple(x['V']);assert raw or isinstance(x['V'],list)
   key=(A,B,vv)
   if key not in choices:choices.append(key)
  text=f"""import CatalanCore.Uniform.Bank.Sevenths.RankCount.{name}
import CatalanCore.Uniform.Bank.Sevenths.RankFacts.{name}
import CatalanCore.Uniform.Bank.Sevenths.RankFinish
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
import CatalanCore.Uniform.Bank.Sevenths.Roots
import CatalanCore.Uniform.Content.RankProducer.LineBound
"""
  if vs:text+=f'import CatalanCore.Uniform.Bank.Sevenths.RankMatch.{name}\n'
  text+="""set_option Elab.async false
set_option maxHeartbeats 2000000
namespace CatalanCore.Uniform.Bank.Sevenths.RankPrice
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
open CatalanCore.Uniform.Content.RankProducer CatalanCore.Uniform.Content.RankProducer.Geometry
open RankFibre RankData RankCount RankFacts
open scoped Classical
"""
  if vs:text+='open RankMatch\n'
  denoms=', '.join(names[t]+'_den' for t in sorted({x['type_id'] for x in c['runs']},key=lambda t:names[t]))
  for qi,(A,B,vv) in enumerate(choices):
   vn=f'{name}_V{vs.index(vv)}' if vv else '((1, 0) : ℚ × ℚ)'
   args='(seventhNumerator a) p r m s ha hp64 hp7 hrp hm1'
   text+=f"""
theorem {name}_member{qi} (a : Fin 6) (p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (hp : rankPrimeCutoff < p) (hr : r % 2 = 0) (hodd : p % 2 = 1)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6) (hm2 : r ≤ 12 * m + 6)
    (hleft : {u.numerator} * r ≤ {u.denominator} * p)
    (hright : {v.denominator} * p ≤ {v.numerator} * r)
    (hroot : 7 * (seventhRho a p - 1) + seventhNumerator a = {root} * p) :
    ∃ M : RankMember (pipelineFrame a) (u7 a) q7 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      (M.price : ℚ) ≤ {aff(A,B)} + 1000 * (((r - s.card : ℕ) : ℚ) + 1) := by
  have hp64 : 64 ≤ p := rankPrimeCutoff_ge_sixtyFour.trans hp.le
  have ha : 1 ≤ seventhNumerator a ∧ seventhNumerator a ≤ 6 := by
    dsimp [seventhNumerator]
    have := a.isLt
    omega
  have hp7 : ¬ p ∣ 7 := by
    intro hd
    have := Nat.le_of_dvd (by norm_num : 0 < 7) hd
    omega
  let PS := seventhsPoleSplit (seventhNumerator a) p r m ha hp64 hp7 hrp hm1
  let cert := {name}_assignment {args}
  have hden : ∀ N ∈ ([{denoms}] : List ℕ), ¬ p ∣ N := by
    intro N hN hd
    have hb : ∀ N ∈ ([{denoms}] : List ℕ), 0 < N ∧ N ≤ rankPrimeCutoff := by decide +kernel
    have hle := Nat.le_of_dvd (hb N hN).1 hd
    have hbound := (hb N hN).2
    omega
  have hb := seventhRho_bounds a p (by omega)
  have hdata (x : ZMod p) := {name}_assignment_valid {args}
    hr hodd hm2 hleft hright (seventhRho a p - 1) (by omega) hroot hden x
  have hOk : ∀ x, (cert x).Ok := fun x => (hdata x).1
  have hInt : ∀ x, (cert x).Integral p := fun x => (hdata x).2.1
  have hReal : ∀ x, Realizes PS (rowsOf r m s) (colsOf r m s) x (cert x) := fun x => (hdata x).2.2
  have hOR := killRows_card_eq_sum PS (rowsOf r m s) (colsOf r m s) (rows_inj r m s) cert hOk hReal
  have hOC := killCols_card_eq_sum PS (rowsOf r m s) (colsOf r m s) (cols_inj r m s) cert hOk hReal
  have hR : {aff(K1,K2)} - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      ((killRows (p := p) (rowsOf r m s) cert).card : ℚ) ∧
      ((killRows (p := p) (rowsOf r m s) cert).card : ℚ) ≤ {aff(K1,K2)} + 48 := by
    rw [hOR]
    exact {name}_row_bounds {args} hleft hright
  have hC : {aff(K1,K2)} - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤
      ((killCols (p := p) (colsOf r m s) cert).card : ℚ) ∧
      ((killCols (p := p) (colsOf r m s) cert).card : ℚ) ≤ {aff(K1,K2)} + 48 := by
    rw [hOC]
    exact {name}_col_bounds {args} hleft hright
  have hFacts (x : ZMod p) := {name}_load_facts {args} hp x
  let V : ℚ × ℚ := {vn}
  have hV1 : V.1 ∈ S p := rank_rational_mem p V.1 hp (by decide +kernel)
  have hV2 : V.2 ∈ S p := rank_rational_mem p V.2 hp (by decide +kernel)
  have hV : castV p V ≠ 0 := rank_castV_ne_zero_of_fst p V hp
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  obtain ⟨M, hK, hcost, htrim⟩ := balanced_rank_line a p r m s hp64 hp7 hrp hm1
    cert hOk hInt hReal (fun x => (hFacts x).1.1) (fun x => (hFacts x).1.2)
    V hV1 hV2 hV (fun x => (hFacts x).2.1)
    (fun x d hd => ⟨((hFacts x).2.2 d hd).1, ((hFacts x).2.2 d hd).2.1⟩)
    (fun x d hd => ((hFacts x).2.2 d hd).2.2)
  have hs : (s.card : ℚ) ≤ r := by exact_mod_cast (show s.card ≤ r by simpa using Finset.card_le_univ s)
  have hm : (12 : ℚ) * m ≤ r + 6 := by exact_mod_cast hm1
  have hdepth : (0 : ℚ) ≤ ((r - s.card : ℕ) : ℚ) := Nat.cast_nonneg _
"""
   if vv:
    weights={side:[sum(Q(z[0])*Q(vv[1])-Q(z[1])*Q(vv[0])==0 for z in case['types'][run['type_id']][side+'_loads']) for run in c['runs']] for side in ['row','column']}
    RA=sum(Q(run['count']['intercept'])*(weights['row'][i]+weights['column'][i]) for i,run in enumerate(c['runs']));RB=sum(Q(run['count']['slope'])*(weights['row'][i]+weights['column'][i]) for i,run in enumerate(c['runs']));assert A==Q(13,6)-RA and B==-RB,(name,qi,A,B,RA,RB)
    vi=vs.index(vv)
    text+=f"""  have hW := {name}_V{vi}_matched_lower {args} hleft hright
  have htrim' : (∑ x : ZMod p, rationalRowMatches (cert x) V) +
      (∑ x : ZMod p, rationalColMatches (cert x) V) ≤ M.colScore + M.rowScore +
      ((killRows (p := p) (rowsOf r m s) cert).card - M.killCount) +
      ((killCols (p := p) (colsOf r m s) cert).card - M.killCount) := by omega
  have hP := price_le_line_of_counts M.price M.killCount
    (killRows (p := p) (rowsOf r m s) cert).card
    (killCols (p := p) (colsOf r m s) cert).card M.colScore M.rowScore
    ((∑ x : ZMod p, rationalRowMatches (cert x) V) + (∑ x : ZMod p, rationalColMatches (cert x) V))
    (s.card + m) {aff(K1,K2)} (48 + 8 * ((r - s.card : ℕ) : ℚ)) 48
    {aff(RA,RB)} (96 + 16 * ((r - s.card : ℕ) : ℚ)) hK hcost htrim' hR hC hW
  exact ⟨M, by push_cast at hP; linarith⟩
"""
   else:
    text+=f"""  have hmin : {aff(K1,K2)} - (48 + 8 * ((r - s.card : ℕ) : ℚ)) ≤ (M.killCount : ℚ) := by
    rw [hK]
    rcases le_total (killRows (p := p) (rowsOf r m s) cert).card
        (killCols (p := p) (colsOf r m s) cert).card with h | h
    · rw [min_eq_left h]; exact hR.1
    · rw [min_eq_right h]; exact hC.1
  have hraw : M.price + M.killCount ≤ 2 * (s.card + m) := by omega
  have hrawQ : (M.price : ℚ) + (M.killCount : ℚ) ≤ 2 * ((s.card : ℚ) + m) := by exact_mod_cast hraw
  exact ⟨M, by linarith⟩
"""
   text+=f'\n#print axioms {name}_member{qi}\n'
  text+='end CatalanCore.Uniform.Bank.Sevenths.RankPrice\n';(O/(name+'.lean')).write_text(text,encoding='utf-8')
  print('Prepared actual producer prices',name,len(choices))
(S/'prices-manifest.json').write_text(json.dumps(manifest,indent=2))
