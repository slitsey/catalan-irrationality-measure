/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/AffineInverseDifferential.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Base.RestrictedAffineInverse

set_option backward.privateInPublic true

@[expose] public section

/-! U/V on an affine inverse are computed from its independently constructed
power series and the formal derivative product rule. -/
namespace CatalanCore.Li2.Port.Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma affineInverseSeries_square (a : ℤ_[p]ˣ) (b : ℤ_[p]) :
    (affineInverseSeries a b 1)^2 = affineInverseSeries a b 2 := by
  unfold affineInverseSeries
  rw [mul_pow, inverseOneSubSeries_square]
  simp only [pow_one, map_pow]

theorem affineInverseSeries_derivative_one (a : ℤ_[p]ˣ) (b : ℤ_[p]) :
    PowerSeries.derivative (R := ℤ_[p]) (affineInverseSeries a b 1) =
      PowerSeries.C (-b)*affineInverseSeries a b 2 := by
  have h := affineInverseSeries_identity a b 1
  rw [pow_one] at h
  have hd := (PowerSeries.derivative (R := ℤ_[p])).leibniz_of_mul_eq_one h
  simp only [map_add, Derivation.leibniz, PowerSeries.derivative_C,
    PowerSeries.derivative_X, smul_eq_mul, mul_one, mul_zero, zero_add, add_zero,
    affineInverseSeries_square] at hd
  simpa only [map_neg, neg_mul, mul_neg, mul_comm] using hd

theorem affineInverseSeries_X_derivative (a : ℤ_[p]ˣ) (b : ℤ_[p]) :
    PowerSeries.derivative (R := ℤ_[p]) (PowerSeries.X*affineInverseSeries a b 1) =
      PowerSeries.C (a:ℤ_[p])*affineInverseSeries a b 2 := by
  have h := affineInverseSeries_identity a b 1
  rw [pow_one] at h
  have hf : affineInverseSeries a b 1 =
      (PowerSeries.C (a:ℤ_[p])+PowerSeries.C b*PowerSeries.X)*affineInverseSeries a b 2 := by
    rw [← affineInverseSeries_square]
    calc
      _ = affineInverseSeries a b 1*(affineInverseSeries a b 1*
          (PowerSeries.C (a:ℤ_[p])+PowerSeries.C b*PowerSeries.X)) := by rw [h, mul_one]
      _ = _ := by ring
  rw [Derivation.leibniz, PowerSeries.derivative_X,
    affineInverseSeries_derivative_one, smul_eq_mul, smul_eq_mul, mul_one, map_neg]
  rw [hf]
  ring

theorem restrictedU_affine_inverse (μ : ℕ → ℤ_[p])
    (a : ℤ_[p]ˣ) (b : ℤ_[p]) (hb : ‖b‖ < 1) :
    restrictedU μ (affineInverseSeries a b 1) =
      (a:ℤ_[p])*restrictedMoment μ (affineInverseSeries a b 2) := by
  rw [restrictedU_derivative, affineInverseSeries_X_derivative, ← PowerSeries.smul_eq_C_mul]
  exact restrictedMoment_smul μ _ (affineInverseSeries_isRestricted a b hb 2) _

theorem restrictedV_affine_inverse (μ : ℕ → ℤ_[p])
    (a : ℤ_[p]ˣ) (b : ℤ_[p]) (hb : ‖b‖ < 1) :
    restrictedV μ (affineInverseSeries a b 1) =
      -b*restrictedMoment μ (affineInverseSeries a b 2) := by
  rw [restrictedV_derivative μ _ (affineInverseSeries_isRestricted a b hb 1),
    affineInverseSeries_derivative_one, ← PowerSeries.smul_eq_C_mul]
  exact restrictedMoment_smul μ _ (affineInverseSeries_isRestricted a b hb 2) _

end
end CatalanCore.Li2.Port.Li2

end
