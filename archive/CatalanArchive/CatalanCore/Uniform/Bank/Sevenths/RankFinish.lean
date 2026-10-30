import CatalanCore.Uniform.Bank.Sevenths.RankSetup
import CatalanCore.Uniform.Content.RankProducer.LineTrim
import CatalanCore.Uniform.Content.RankProducer.LineCost
import CatalanCore.Uniform.Content.RankProducer.ActiveFibres
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open Finset Module CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
open CatalanCore.Uniform.Content.RankProducer CatalanCore.Uniform.Content.Member
open CatalanCore.Uniform.Content.RankProducer.Geometry
open scoped Classical

/-- Complete balanced member and line bookkeeping for an actual pipeline assignment. -/
theorem balanced_rank_line (a : Fin 6) (p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
    (hReal : ∀ x, Realizes (seventhsPoleSplit (seventhNumerator a) p r m (by dsimp [seventhNumerator]; omega) hp64 hp7 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x (cert x))
    (hRs : ∀ x, (cert x).kr.card ≤ 1) (hCs : ∀ x, (cert x).kc.card ≤ 1)
    (v : ℚ × ℚ) (hv1 : v.1 ∈ S p) (hv2 : v.2 ∈ S p) (hv : castV p v ≠ 0)
    (hRu : ∀ x, ∀ d ∈ (cert x).kr, ((cert x).rload d).1 ∈ S p ∧ ((cert x).rload d).2 ∈ S p)
    (hCu : ∀ x, ∀ d ∈ (cert x).kc, ((cert x).cload d).1 ∈ S p ∧ ((cert x).cload d).2 ∈ S p)
    (hCn : ∀ x, ∀ d ∈ (cert x).kc, castV p ((cert x).cload d) ≠ 0) :
    ∃ M : RankMember (pipelineFrame a) (u7 a) q7 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      M.killCount = min (killRows (p := p) (rowsOf r m s) cert).card
        (killCols (p := p) (colsOf r m s) cert).card ∧
      M.price + max M.killCount (M.colScore + M.rowScore) ≤ 2 * (s.card + m) ∧
      (∑ x : ZMod p, rationalRowMatches (cert x) v) +
        (∑ x : ZMod p, rationalColMatches (cert x) v) ≤ M.rowScore + M.colScore +
          ((killRows (p := p) (rowsOf r m s) cert).card - M.killCount) +
          ((killCols (p := p) (colsOf r m s) cert).card - M.killCount) := by
  let A := rowsOf r m s
  let B := colsOf r m s
  let PS := seventhsPoleSplit (seventhNumerator a) p r m (by dsimp [seventhNumerator]; omega) hp64 hp7 hrp hm1
  have hA : Function.Injective A := rows_inj r m s
  have hB : Function.Injective B := cols_inj r m s
  obtain ⟨KR, KC, hKR, hKC, hRcard, hCcard⟩ :=
    CatalanCore.Uniform.Content.RankProducer.exists_balanced_indices A B cert
  let bal := CatalanCore.Uniform.Content.RankProducer.retainAssignment A B cert KR KC
  have hBO (x : ZMod p) : (bal x).Ok :=
    CatalanCore.Uniform.Content.RankProducer.retainAssignment_ok A B cert hOk KR KC hKR hKC x
  have hBI (x : ZMod p) : (bal x).Integral p :=
    CatalanCore.Uniform.Content.RankProducer.trim_integral (cert x) p (hInt x) _ _
  have hBR (x : ZMod p) : Realizes PS A B x (bal x) :=
    CatalanCore.Uniform.Content.RankProducer.trim_realizes PS A B x (cert x) (hReal x) _ _
  have hKRbal : killRows (p := p) A bal = KR :=
    CatalanCore.Uniform.Content.RankProducer.retainAssignment_killRows A B hA cert KR KC
  have hKCbal : killCols (p := p) B bal = KC :=
    CatalanCore.Uniform.Content.RankProducer.retainAssignment_killCols A B hB cert KR KC
  have hcard : (killRows (p := p) A bal).card = (killCols (p := p) B bal).card := by
    rw [hKRbal, hKCbal, hRcard, hCcard]
  let M := rankMemberOfAssignment a p r m s hp64 hp7 hrp hm1 bal hBO hBI hBR hcard (castV p v) hv
  have hMK : M.killCount = min (killRows (p := p) A cert).card (killCols (p := p) B cert).card := by
    change (killRows (p := p) A bal).card = _
    rw [hKRbal]
    exact hRcard
  have hsmallR (x : ZMod p) : (bal x).kr.card ≤ 1 :=
    (Finset.card_le_card (CatalanCore.Uniform.Content.RankProducer.retained_rows_sub A cert KR hKR x)).trans (hRs x)
  have hsmallC (x : ZMod p) : (bal x).kc.card ≤ 1 :=
    (Finset.card_le_card (CatalanCore.Uniform.Content.RankProducer.retained_cols_sub B cert KC hKC x)).trans (hCs x)
  have hdim : finrank (RatFunc (ZMod p)) M.Vs = 1 := by
    change finrank (RatFunc (ZMod p)) (Submodule.span (RatFunc (ZMod p)) {castV p v}) = 1
    exact finrank_span_singleton hv
  have hcost : M.price + max M.killCount (M.colScore + M.rowScore) ≤ 2 * (s.card + m) := by
    simpa only [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin] using
      M.price_line_bound hdim hsmallR hsmallC
  have hrowScore : M.rowScore =
      ∑ x ∈ KR.image (fun i => (A i : ZMod p)), lineMr p (bal x) (castV p v) := by
    unfold RankMember.rowScore
    rw [rowFib_eq_image]
    change (∑ x ∈ (killRows (p := p) A bal).image (fun i => (A i : ZMod p)),
      lineMr p (bal x) (castV p v)) = _
    rw [hKRbal]
  have hcolScore : M.colScore =
      ∑ x ∈ KC.image (fun i => (B i : ZMod p)), lineMc p (bal x) (castV p v) := by
    unfold RankMember.colScore
    rw [colFib_eq_image]
    change (∑ x ∈ (killCols (p := p) B bal).image (fun i => (B i : ZMod p)),
      lineMc p (bal x) (castV p v)) = _
    rw [hKCbal]
  have hrow := matching_killRows_eq_sum PS A B hA cert hOk hReal
    (fun x d => ((cert x).rload d).1 * v.2 - ((cert x).rload d).2 * v.1 = 0)
  have hcol := matching_killCols_eq_sum PS A B hB cert hOk hReal
    (fun x d => ((cert x).cload d).1 * v.2 - ((cert x).cload d).2 * v.1 = 0)
  have htrim := trim_matching_scores A B hA hB cert KR KC hKR hKC hRs hCs v hv1 hv2 hv hRu hCu hCn
  dsimp only at htrim
  rw [hrow, hcol, ← hrowScore, ← hcolScore] at htrim
  refine ⟨M, hMK, hcost, ?_⟩
  simpa only [rationalRowMatches, rationalColMatches, hMK, hRcard, hCcard] using htrim

#print axioms balanced_rank_line
end CatalanCore.Uniform.Bank.Sevenths
