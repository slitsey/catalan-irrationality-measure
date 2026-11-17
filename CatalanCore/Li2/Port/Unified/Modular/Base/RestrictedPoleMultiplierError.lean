/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/RestrictedPoleMultiplierError.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Base.RestrictedSeriesCompat
public import CatalanCore.Li2.Port.Unified.Modular.Base.RestrictedPoleMultiplierBounds

set_option backward.privateInPublic true

@[expose] public section

/-! Exact decomposition of multiplication by g into its chosen constant and
a coefficientwise small error, in the existing simple-pole representation. -/
namespace CatalanCore.Li2.Port.Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integralPoleMultiplier_decomposition (c : ι → ℤ_[p])
    (hc : Function.Injective c) (g f : PowerSeries ℤ_[p])
    (hg : PowerSeries.IsRestricted 1 g) (hf : PowerSeries.IsRestricted 1 f)
    (r : ι → ℤ_[p]) (k : ℤ_[p]) :
    integralPoleMulRegular c g f r = k • f +
      integralPoleMulRegular c (g-PowerSeries.C k) f r ∧
    integralPoleMulResidue c g r = k • r +
      integralPoleMulResidue c (g-PowerSeries.C k) r := by
  have he : PowerSeries.IsRestricted 1 (g-PowerSeries.C k) := by
    rw [sub_eq_add_neg]
    exact PowerSeries.isRestricted.add 1 hg
      (PowerSeries.isRestricted.neg 1 (PowerSeries.isRestricted_C 1 k))
  apply integralPoleNumerator_injective c hc _ _
    (integralPoleMulRegular_isRestricted c g f hg hf r)
    (PowerSeries.isRestricted.add 1 (CatalanCore.Li2.Port.Li2.restrictedSeries_smul 1 hf k)
      (integralPoleMulRegular_isRestricted c _ f he hf r))
  rw [integralPoleNumerator_mul c g f hg r, integralPoleNumerator_add,
    integralPoleNumerator_smul, integralPoleNumerator_mul c _ f he r]
  ring

theorem integralPoleMultiplier_regular_error (c : ι → ℤ_[p])
    (hc : Function.Injective c) (g f : PowerSeries ℤ_[p])
    (hg : PowerSeries.IsRestricted 1 g) (hf : PowerSeries.IsRestricted 1 f)
    (r : ι → ℤ_[p]) (k : ℤ_[p]) (B : ℝ) (hB : 0 ≤ B)
    (he : ∀ n, ‖PowerSeries.coeff n (g-PowerSeries.C k)‖ ≤ B) (n : ℕ) :
    ‖PowerSeries.coeff n (integralPoleMulRegular c g f r-k • f)‖ ≤ B := by
  rw [(integralPoleMultiplier_decomposition c hc g f hg hf r k).1,
    add_sub_cancel_left]
  exact integralPoleMulRegular_bound_left c _ f r B hB he n

theorem integralPoleMultiplier_residue_error (c : ι → ℤ_[p])
    (hc : Function.Injective c) (g f : PowerSeries ℤ_[p])
    (hg : PowerSeries.IsRestricted 1 g) (hf : PowerSeries.IsRestricted 1 f)
    (r : ι → ℤ_[p]) (k : ℤ_[p]) (B : ℝ)
    (he : ∀ n, ‖PowerSeries.coeff n (g-PowerSeries.C k)‖ ≤ B) (i : ι) :
    ‖integralPoleMulResidue c g r i-k*r i‖ ≤ B := by
  rw [(integralPoleMultiplier_decomposition c hc g f hg hf r k).2]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
  exact integralPoleMulResidue_bound_left c _ r B he i

end
end CatalanCore.Li2.Port.Li2

end
