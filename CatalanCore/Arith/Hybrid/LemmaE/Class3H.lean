module

public import CatalanCore.Arith.Hybrid.LemmaE.Class3G

@[expose] public section

/-!
# Lemma E, class 3: `M0 = pairMatG ...` is invertible, `D1 = 1`
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime] {r m k1 : ℕ}

variable (S : ESetup3 p r m k1)

lemma rfC_ne_zero {x : ZMod p} (h : x ≠ 0) : rfC p x ≠ 0 := by
  rw [rfC_eq]; exact (map_ne_zero (rfCH p)).2 h

include S

lemma M0_eq : (Matrix.of fun c c' : Pt3 p r m =>
      Mat3 p r m (sd3 S) (Sum.inl (Sum.inl c)) (Sum.inl (Sum.inl c'))) =
    pairMatG (tau3 S) (fun c => rfC p (dZ S c.1.val)) (fun c => rfC p (eZ S c.1.val)) := by
  ext c c'
  simp only [Matrix.of_apply, Mat3_pp]
  rw [TE3_PP S c.1.2 c.2 c'.1.2 c'.2]
  unfold pairMatG
  simp only [Matrix.of_apply]
  by_cases h1 : c' = c
  · subst h1; simp
  · have h1' : (c'.1 : ℕ) ≠ c.1 := fun h => h1 (Subtype.ext (Fin.ext h))
    rw [if_neg h1', if_neg h1]
    by_cases h3 : c' = tau3 S c
    · have h3' : (c'.1 : ℕ) = tauN p r c.1 := by rw [h3]; rfl
      rw [if_pos h3', if_pos h3]
    · have h3' : (c'.1 : ℕ) ≠ tauN p r c.1 := fun h => h3 (Subtype.ext (Fin.ext (by rw [h]; rfl)))
      rw [if_neg h3', if_neg h3, rfC_zero]

noncomputable def M0_invertible (h3 : (3 : ZMod p) ≠ 0) (h5 : (5 : ZMod p) ≠ 0)
    (h6255 : (6255 : ZMod p) ≠ 0) :
    Invertible (Matrix.of fun c c' : Pt3 p r m =>
      Mat3 p r m (sd3 S) (Sum.inl (Sum.inl c)) (Sum.inl (Sum.inl c'))) := by
  have hk1 := S.hk1
  have hpr := S.hpr
  have hk2r := S.hk2r
  have hN := S.hN
  rw [M0_eq S]
  refine invertibleOfRightInverse _ (pairInvG (tau3 S) (fun c => rfC p (dZ S c.1.val))
    (fun c => rfC p (eZ S c.1.val))) (pairMatG_mul_pairInvG (tau3 S) _ _ (tau3_invol S) ?_ ?_ ?_)
  · intro c
    show rfC p (eZ S (tauN p r c.1.val)) = rfC p (eZ S c.1.val)
    rw [eZ_tau S c.1.2 c.2]
  · intro c hc
    have hc' := (tau3_fix S c).1 hc
    apply rfC_ne_zero
    rw [dZ_B1 S (a := c.1.val) (by have := c.2; have h6 := c.1.2; unfold isCz at this; omega) (by omega)]
    exact one_ne_zero
  · intro c hc
    have hΔ : dZ S c.1.val * dZ S (tauN p r c.1.val) - eZ S c.1.val ^ 2 ≠ 0 := by
      have hne : ¬ (¬ ((c.1 : ℕ) < r - p) ∧ ¬ (p ≤ (c.1 : ℕ))) := fun h => hc ((tau3_fix S c).2 h)
      by_cases hlt : (c.1 : ℕ) < r - p
      · have ht : tauN p r c.1.val = c.1.val + p := by unfold tauN; rw [if_pos hlt]
        rw [ht]
        exact delta_core S hlt h3 h5 h6255
      · have hp : p ≤ (c.1 : ℕ) := by
          by_contra hh; exact hne ⟨hlt, hh⟩
        have ht : tauN p r c.1.val = c.1.val - p := by
          unfold tauN; rw [if_neg hlt, if_pos hp]
        have hlt2 : c.1.val - p < r - p := by have := c.1.2; omega
        have key := delta_core S hlt2 h3 h5 h6255
        rw [Nat.sub_add_cancel hp] at key
        have he := eZ_tau S c.1.2 c.2
        rw [ht] at he ⊢
        rw [← he]
        intro hh; apply key
        rw [← hh]; ring
    show rfC p (dZ S c.1.val) * rfC p (dZ S (tauN p r c.1.val)) - rfC p (eZ S c.1.val) ^ 2 ≠ 0
    rw [rfC_eq, rfC_eq, rfC_eq, ← map_mul, ← map_pow, ← map_sub]
    exact (map_ne_zero (rfCH p)).2 hΔ

end

end CatalanCore.Arith.Hybrid
