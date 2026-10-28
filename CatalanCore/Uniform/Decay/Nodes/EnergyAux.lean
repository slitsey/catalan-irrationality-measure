module
public import CatalanLambda.Decay.ThmNDecomp
@[expose] public section

/-!
# Auxiliary pointwise facts for the block-node energy step
-/

namespace CatalanCore.Uniform.Decay.Nodes
open Finset CatalanLambda.Decay

/-- Lower bound `U^σ_ρ(s) ≥ -(‖s‖ + R_c + ρ)` for a probability weight (local copy of `Usig_ge`,
which lives in the stale Decay tree). -/
theorem Usig_ge' {K : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (c : Fin K → ℂ) (wt : Fin K → ℝ)
    (hw0 : ∀ k, 0 ≤ wt k) (hw1 : ∑ k, wt k = 1) {Rc : ℝ} (hc : ∀ k, ‖c k‖ ≤ Rc) (s : ℂ) :
    -(‖s‖ + Rc + ρ) ≤ Usig ρ c wt s := by
  have hRc : 0 ≤ Rc := by
    by_cases hK : Nonempty (Fin K)
    · obtain ⟨k⟩ := hK; exact (norm_nonneg _).trans (hc k)
    · exfalso; simp at hK; subst hK; simp at hw1
  set X : ℝ := ‖s‖ + Rc + ρ with hX
  have hX0 : 0 < X := by have := norm_nonneg s; positivity
  have key : ∀ k, -X ≤ krho ρ s (c k) := by
    intro k
    unfold krho
    have h1 : ‖s - c k‖ ≤ ‖s‖ + Rc := (norm_sub_le _ _).trans (by linarith [hc k])
    have h2 : ‖s - c k‖ ^ 2 + ρ ^ 2 ≤ X ^ 2 := by
      have := norm_nonneg (s - c k)
      nlinarith [norm_nonneg s]
    have h3 : Real.log (‖s - c k‖ ^ 2 + ρ ^ 2) ≤ Real.log (X ^ 2) :=
      Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h3
    have h4 := Real.log_le_sub_one_of_pos hX0
    push_cast at h3
    linarith
  unfold Usig
  calc -X = ∑ k, wt k * (-X) := by rw [← Finset.sum_mul, hw1]; ring
    _ ≤ _ := Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (key k) (hw0 k))

/-- Upper bound `U^σ_ρ ≤ -log ρ` for a probability weight. -/
theorem Usig_le {K : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (c : Fin K → ℂ) (wt : Fin K → ℝ)
    (hw0 : ∀ k, 0 ≤ wt k) (hw1 : ∑ k, wt k = 1) (s : ℂ) :
    Usig ρ c wt s ≤ -Real.log ρ := by
  have key : ∀ k, krho ρ s (c k) ≤ -Real.log ρ := by
    intro k
    unfold krho
    have h : Real.log (ρ ^ 2) ≤ Real.log (‖s - c k‖ ^ 2 + ρ ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith [sq_nonneg ‖s - c k‖])
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  unfold Usig
  calc ∑ k, wt k * krho ρ s (c k) ≤ ∑ k, wt k * (-Real.log ρ) :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (key k) (hw0 k))
    _ = -Real.log ρ := by rw [← Finset.sum_mul, hw1]; ring

/-- `|U^σ_ρ(s)| ≤ ‖s‖ + R_c + ρ + |log ρ|`. -/
theorem abs_Usig_le {K : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (c : Fin K → ℂ) (wt : Fin K → ℝ)
    (hw0 : ∀ k, 0 ≤ wt k) (hw1 : ∑ k, wt k = 1) {Rc : ℝ} (hc : ∀ k, ‖c k‖ ≤ Rc) (s : ℂ) :
    |Usig ρ c wt s| ≤ ‖s‖ + Rc + ρ + |Real.log ρ| := by
  have h1 := Usig_ge' hρ c wt hw0 hw1 hc s
  have h2 := Usig_le hρ c wt hw0 hw1 s
  have h3 : -Real.log ρ ≤ |Real.log ρ| := neg_le_abs _
  have hn := norm_nonneg s
  have hR : 0 ≤ Rc := by
    by_cases hK : Nonempty (Fin K)
    · obtain ⟨k⟩ := hK; exact (norm_nonneg _).trans (hc k)
    · exfalso; simp at hK; subst hK; simp at hw1
  have h4 := abs_nonneg (Real.log ρ)
  rw [abs_le]
  constructor <;> linarith

/-- The pointwise inequality replacing `N` by `M r` at a free point or removed node. -/
theorem pt_block {r N M Y U g Kc A im ε : ℝ} (hr : 0 < r) (hN : |N - M * r| ≤ Kc)
    (hY : |Y| ≤ A) (hg : g = M * Y - U + (1 - ε) * Real.pi * |im| / r) :
    2 * r * g - 2 * (1 - ε) * Real.pi * |im| - 2 * Kc * A ≤ 2 * N * Y - 2 * r * U := by
  have h1 : |(N - M * r) * Y| ≤ Kc * A := by
    rw [abs_mul]
    exact mul_le_mul hN hY (abs_nonneg _) ((abs_nonneg _).trans hN)
  have h2 : 2 * r * g = 2 * r * (M * Y - U) + 2 * (1 - ε) * Real.pi * |im| := by
    rw [hg]; field_simp
  have h3 := (abs_le.mp h1).1
  nlinarith [h3]

end CatalanCore.Uniform.Decay.Nodes
