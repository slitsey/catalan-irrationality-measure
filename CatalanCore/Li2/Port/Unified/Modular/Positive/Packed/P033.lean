/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Positive/Packed/P033.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P028
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P032

set_option backward.privateInPublic true

@[expose] public section

section
namespace CatalanCore.Li2.Port.Unified.Proofs.Arithmetic
noncomputable section
open CatalanCore.Li2.Port.Unified.Stage0.HermitePreparation

def profileWindowThetaLo : Fin 6 → ℝ := ![0, 1/4, 1/3, 1/2, 2/3, 3/4]
def profileWindowThetaHi : Fin 6 → ℝ := ![1/4, 1/3, 1/2, 2/3, 3/4, 1]

private theorem reciprocal_half_open_bounds (α β x : ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (hleft : β⁻¹ < x) (hright : x ≤ α⁻¹) :
    0 < x ∧ α ≤ x⁻¹ ∧ x⁻¹ < β := by
  have hx : 0 < x := (inv_pos.mpr hβ).trans hleft
  have hαx : α ≤ x⁻¹ := by
    have := (inv_le_inv₀ (inv_pos.mpr hα) hx).2 hright
    simpa using! this
  have hxβ : x⁻¹ < β := by
    have := (inv_lt_inv₀ hx (inv_pos.mpr hβ)).2 hleft
    simpa using! this
  exact ⟨hx, hαx, hxβ⟩

private theorem window_left_reciprocal (A : ℝ) (hA : 1 ≤ A) (j : Fin 6) :
    profileWindowLeft A j = (A+profileWindowThetaHi j)⁻¹ := by
  fin_cases j <;> norm_num [profileWindowLeft, profileWindowThetaHi]
  all_goals
    have hApos : 0 < A := by linarith
    field_simp

private theorem window_right_reciprocal (A : ℝ) (hA : 1 ≤ A) (j : Fin 6) :
    profileWindowRight A j = (A+profileWindowThetaLo j)⁻¹ := by
  fin_cases j <;> norm_num [profileWindowRight, profileWindowThetaLo]
  all_goals
    have hApos : 0 < A := by linarith
    field_simp

/-- Exact profile formula at every point of a half-open prime window,
including all floor jump endpoints. -/
theorem profile_window_half_open (A : ℕ) (hA : 1 ≤ A)
    (j : Fin 6) (x : ℝ)
    (hl : profileWindowLeft A j < x)
    (hr : x ≤ profileWindowRight A j) :
    profile x = profileWindowAlpha A j * x + profileWindowBeta A j := by
  have hAr : (1:ℝ) ≤ A := by exact_mod_cast hA
  have hα : 0 < (A:ℝ)+profileWindowThetaLo j := by
    fin_cases j <;> norm_num [profileWindowThetaLo] <;> linarith
  have hβ : 0 < (A:ℝ)+profileWindowThetaHi j := by
    fin_cases j <;> norm_num [profileWindowThetaHi] <;> linarith
  rw [window_left_reciprocal A hAr j] at hl
  rw [window_right_reciprocal A hAr j] at hr
  obtain ⟨hx, hθlo, hθhi⟩ := reciprocal_half_open_bounds
    ((A:ℝ)+profileWindowThetaLo j)
    ((A:ℝ)+profileWindowThetaHi j) x hα hβ hl hr
  fin_cases j
  · norm_num [profileWindowThetaLo, profileWindowThetaHi,
      profileWindowAlpha, profileWindowBeta] at hθlo hθhi ⊢
    rw [profile_piece_zero_closed A x hx hθlo hθhi]
    ring
  · norm_num [profileWindowThetaLo, profileWindowThetaHi,
      profileWindowAlpha, profileWindowBeta] at hθlo hθhi ⊢
    rw [profile_piece_one_closed A x hx hθlo hθhi]
    ring
  · norm_num [profileWindowThetaLo, profileWindowThetaHi,
      profileWindowAlpha, profileWindowBeta] at hθlo hθhi ⊢
    rw [profile_piece_two_closed A x hx hθlo hθhi]
    ring
  · norm_num [profileWindowThetaLo, profileWindowThetaHi,
      profileWindowAlpha, profileWindowBeta] at hθlo hθhi ⊢
    rw [profile_piece_three_closed A x hx hθlo hθhi]
    ring
  · norm_num [profileWindowThetaLo, profileWindowThetaHi,
      profileWindowAlpha, profileWindowBeta] at hθlo hθhi ⊢
    rw [profile_piece_four_closed A x hx hθlo hθhi]
    ring
  · norm_num [profileWindowThetaLo, profileWindowThetaHi,
      profileWindowAlpha, profileWindowBeta] at hθlo hθhi ⊢
    rw [profile_piece_five_closed A x hx hθlo hθhi]
    ring

end
end CatalanCore.Li2.Port.Unified.Proofs.Arithmetic

#print axioms CatalanCore.Li2.Port.Unified.Proofs.Arithmetic.profile_window_half_open

end


end
