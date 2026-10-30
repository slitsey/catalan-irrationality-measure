import CatalanCore.Uniform.Content.RankProducer.LineScores
import CatalanCore.Uniform.Content.RankProducer.TrimCost
import CatalanCore.Uniform.Content.RankProducer.Balance
import CatalanCore.Uniform.Content.RankProducer.RationalMatches
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open Finset Module CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
open scoped Classical
variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual matching coordinates survive arbitrary balancing except for discarded kills. -/
theorem trim_matching_scores (a b : ι → ℕ) (ha : Function.Injective a) (hb : Function.Injective b)
    (cert : ZMod p → FibreCert) (KR KC : Finset ι)
    (hKR : KR ⊆ killRows (p := p) a cert) (hKC : KC ⊆ killCols (p := p) b cert)
    (hRs : ∀ x, (cert x).kr.card ≤ 1) (hCs : ∀ x, (cert x).kc.card ≤ 1)
    (v : ℚ × ℚ) (hv1 : v.1 ∈ S p) (hv2 : v.2 ∈ S p) (hv : castV p v ≠ 0)
    (hRu : ∀ x, ∀ d ∈ (cert x).kr, ((cert x).rload d).1 ∈ S p ∧ ((cert x).rload d).2 ∈ S p)
    (hCu : ∀ x, ∀ d ∈ (cert x).kc, ((cert x).cload d).1 ∈ S p ∧ ((cert x).cload d).2 ∈ S p)
    (hCn : ∀ x, ∀ d ∈ (cert x).kc, castV p ((cert x).cload d) ≠ 0) :
    let bal := retainAssignment a b cert KR KC
    ((killRows (p := p) a cert).filter (fun i =>
      ((cert (a i : ZMod p)).rload (a i / p)).1 * v.2 -
        ((cert (a i : ZMod p)).rload (a i / p)).2 * v.1 = 0)).card +
    ((killCols (p := p) b cert).filter (fun i =>
      ((cert (b i : ZMod p)).cload (b i / p)).1 * v.2 -
        ((cert (b i : ZMod p)).cload (b i / p)).2 * v.1 = 0)).card ≤
      (∑ x ∈ KR.image (fun i => (a i : ZMod p)), lineMr p (bal x) (castV p v)) +
      (∑ x ∈ KC.image (fun i => (b i : ZMod p)), lineMc p (bal x) (castV p v)) +
      ((killRows (p := p) a cert).card - KR.card) +
      ((killCols (p := p) b cert).card - KC.card) := by
  let bal := retainAssignment a b cert KR KC
  let PR : ι → Prop := fun i => ((cert (a i : ZMod p)).rload (a i / p)).1 * v.2 -
    ((cert (a i : ZMod p)).rload (a i / p)).2 * v.1 = 0
  let PC : ι → Prop := fun i => ((cert (b i : ZMod p)).cload (b i / p)).1 * v.2 -
    ((cert (b i : ZMod p)).cload (b i / p)).2 * v.1 = 0
  have hBR : killRows (p := p) a bal = KR := retainAssignment_killRows a b ha cert KR KC
  have hBC : killCols (p := p) b bal = KC := retainAssignment_killCols a b hb cert KR KC
  have hsmallR (x : ZMod p) : (bal x).kr.card ≤ 1 :=
    (Finset.card_le_card (retained_rows_sub a cert KR hKR x)).trans (hRs x)
  have hsmallC (x : ZMod p) : (bal x).kc.card ≤ 1 :=
    (Finset.card_le_card (retained_cols_sub b cert KC hKC x)).trans (hCs x)
  have hIR : Set.InjOn (fun i => (a i : ZMod p)) (KR : Set ι) := by
    intro i hi j hj hij
    have hf := residue_injective_on_killRows a ha cert hRs
    have he := @hf ⟨i, hKR hi⟩ ⟨j, hKR hj⟩ hij
    exact congrArg (fun z : {i // i ∈ killRows (p := p) a cert} => z.1) he
  have hIC : Set.InjOn (fun i => (b i : ZMod p)) (KC : Set ι) := by
    intro i hi j hj hij
    have hf := residue_injective_on_killCols b hb cert hCs
    have he := @hf ⟨i, hKC hi⟩ ⟨j, hKC hj⟩ hij
    exact congrArg (fun z : {j // j ∈ killCols (p := p) b cert} => z.1) he
  have hRscore : (KR.filter PR).card ≤
      ∑ x ∈ KR.image (fun i => (a i : ZMod p)), lineMr p (bal x) (castV p v) := by
    apply card_filter_le_score KR _ (fun i => (a i : ZMod p)) PR _ hIR
      (fun i hi => Finset.mem_image.2 ⟨i, hi, rfl⟩)
    intro i hi hPi
    have hnew : i ∈ killRows (p := p) a bal := by rw [hBR]; exact hi
    have hdnew := (Finset.mem_filter.1 hnew).2
    have hdold := (Finset.mem_filter.1 (hKR hi)).2
    have hload : (bal (a i : ZMod p)).rload (a i / p) =
        (cert (a i : ZMod p)).rload (a i / p) := rfl
    have horth : omegaL (castV p ((bal (a i : ZMod p)).rload (a i / p))) (castV p v) = 0 := by
      rw [hload]
      exact castV_omega_eq_zero p _ v (hRu _ _ hdold).1 (hRu _ _ hdold).2 hv1 hv2 hPi
    rw [lineMr_eq_one_of_single _ _ (hsmallR _) _ hdnew horth] <;> exact le_rfl
  have hCscore : (KC.filter PC).card ≤
      ∑ x ∈ KC.image (fun i => (b i : ZMod p)), lineMc p (bal x) (castV p v) := by
    apply card_filter_le_score KC _ (fun i => (b i : ZMod p)) PC _ hIC
      (fun i hi => Finset.mem_image.2 ⟨i, hi, rfl⟩)
    intro i hi hPi
    have hnew : i ∈ killCols (p := p) b bal := by rw [hBC]; exact hi
    have hdnew := (Finset.mem_filter.1 hnew).2
    have hdold := (Finset.mem_filter.1 (hKC hi)).2
    have hload : (bal (b i : ZMod p)).cload (b i / p) =
        (cert (b i : ZMod p)).cload (b i / p) := rfl
    have hn : castV p ((bal (b i : ZMod p)).cload (b i / p)) ≠ 0 := by
      rw [hload]
      exact hCn _ _ hdold
    have horthQ : v.1 * ((cert (b i : ZMod p)).cload (b i / p)).2 -
        v.2 * ((cert (b i : ZMod p)).cload (b i / p)).1 = 0 := by
      change _ = 0 at hPi
      dsimp only [PC] at hPi
      linear_combination -hPi
    have hV : castV p ((bal (b i : ZMod p)).cload (b i / p)) ∈
        Submodule.span (RatFunc (ZMod p)) {castV p v} := by
      rw [hload]
      exact mem_span_of_omega_eq_zero _ _ hv
        (castV_omega_eq_zero p v _ hv1 hv2 (hCu _ _ hdold).1 (hCu _ _ hdold).2 horthQ)
    rw [lineMc_eq_one_of_mem _ _ _ hdnew hn hV] <;> exact le_rfl
  have hRloss := filter_card_loss (killRows (p := p) a cert) KR hKR PR
  have hCloss := filter_card_loss (killCols (p := p) b cert) KC hKC PC
  change ((killRows (p := p) a cert).filter PR).card +
      ((killCols (p := p) b cert).filter PC).card ≤ _
  omega

#print axioms trim_matching_scores
end CatalanCore.Uniform.Content.RankProducer
