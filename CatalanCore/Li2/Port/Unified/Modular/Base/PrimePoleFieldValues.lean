/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/PrimePoleFieldValues.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Base.PrimePoleExtension

set_option backward.privateInPublic true

@[expose] public section

/-! The existing integral pole polynomials evaluated at arbitrary Qp values.
This keeps the field-valued dissection tied to the actual integral extension. -/
open Polynomial
namespace CatalanCore.Li2.Port.Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

theorem primeUPole_eval₂ (hp2 : p ≠ 2) (j : ℕ) (hj : j < p) (Y : ℚ_[p]) :
    (primeUPole hp2 j hj).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
      (j:ℚ_[p])*(primeParameter p:ℚ_[p])⁻¹^j*
        (Y-(parameterTau (primeParameter p) j:ℚ_[p])) := by
  simp only [primeUPole, integralUPole, eval₂_mul, eval₂_C, eval₂_sub, eval₂_X,
    map_mul, map_neg, map_natCast, PadicInt.algebraMap_apply]
  simp [integralParameterInvPow, integralParameterTau, integralRational]

theorem primeVPole_eval₂ (hp2 : p ≠ 2) (j : ℕ) (hj : j < p) (Y : ℚ_[p]) :
    (primeVPole hp2 j hj).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
      -(primeParameter p:ℚ_[p])⁻¹^j*
        (Y-(parameterTau (primeParameter p) j:ℚ_[p])) := by
  unfold primeVPole integralVPole
  rw [eval₂_mul, eval₂_C, eval₂_sub, eval₂_X, eval₂_C, map_neg,
    PadicInt.algebraMap_apply, PadicInt.algebraMap_apply]
  simp [integralParameterInvPow, integralParameterTau, integralRational]


theorem primePoleU_single_eval₂ (hp4 : 3 < p) (j : Fin 4) (Y : ℚ_[p]) :
    (primePoleU hp4 0 (Pi.single j 1)).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
      (j.val:ℚ_[p])*(primeParameter p:ℚ_[p])⁻¹^j.val*
        (Y-(parameterTau (primeParameter p) j.val:ℚ_[p])) := by
  rw [primePoleU_single, primeUPole_eval₂]

theorem primePoleV_single_eval₂ (hp4 : 3 < p) (j : Fin 4) (Y : ℚ_[p]) :
    (primePoleV hp4 0 (Pi.single j 1)).eval₂ (algebraMap ℤ_[p] ℚ_[p]) Y =
      -(primeParameter p:ℚ_[p])⁻¹^j.val*
        (Y-(parameterTau (primeParameter p) j.val:ℚ_[p])) := by
  rw [primePoleV_single, primeVPole_eval₂]

end
end CatalanCore.Li2.Port.Li2

end
