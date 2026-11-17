/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/RestrictedRationalUnits.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Base.RestrictedFunctional
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Analysis.SpecificLimits.Basic

set_option backward.privateInPublic true

@[expose] public section

/-! Contracting a formal integral series gives a restricted series. Applied to
the existing inverse of (1-X)^d, this controls all nonmatching local factors. -/
open Filter
open scoped Topology BigOperators
namespace CatalanCore.Li2.Port.Li2
noncomputable section
variable {p : ℕ} [Fact p.Prime]

lemma rescale_coeff_norm_le (b : ℤ_[p]) (f : PowerSeries ℤ_[p]) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.rescale b f)‖ ≤ ‖b‖^n := by
  rw [PowerSeries.coeff_rescale, norm_mul, norm_pow]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _)
    (pow_nonneg (norm_nonneg b) n)

theorem rescale_isRestricted (b : ℤ_[p]) (hb : ‖b‖ < 1) (f : PowerSeries ℤ_[p]) :
    PowerSeries.IsRestricted 1 (PowerSeries.rescale b f) := by
  rw [PowerSeries.isRestricted_iff']
  simp only [one_pow, mul_one]
  exact squeeze_zero (fun _ => norm_nonneg _) (rescale_coeff_norm_le b f)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg b) hb)

def inverseOneSubSeries (b : ℤ_[p]) (d : ℕ) : PowerSeries ℤ_[p] :=
  PowerSeries.rescale b (PowerSeries.invOneSubPow (ℤ_[p]) d).val

theorem inverseOneSubSeries_identity (b : ℤ_[p]) (d : ℕ) :
    inverseOneSubSeries b d*(1-PowerSeries.C b*PowerSeries.X)^d = 1 := by
  have h := congrArg (PowerSeries.rescale b) (PowerSeries.invOneSubPow (ℤ_[p]) d).val_inv
  rw [PowerSeries.invOneSubPow_inv_eq_one_sub_pow] at h
  simpa only [inverseOneSubSeries, map_mul, map_pow, map_sub, map_one,
    PowerSeries.rescale_X] using h

theorem inverseOneSubSeries_isRestricted (b : ℤ_[p]) (hb : ‖b‖ < 1) (d : ℕ) :
    PowerSeries.IsRestricted 1 (inverseOneSubSeries b d) :=
  rescale_isRestricted b hb _

lemma inverseOneSubSeries_coeff_zero (b : ℤ_[p]) (d : ℕ) :
    PowerSeries.coeff 0 (inverseOneSubSeries b d) = 1 := by
  cases d <;> simp [inverseOneSubSeries, PowerSeries.invOneSubPow,
    PowerSeries.coeff_rescale]

theorem inverseOneSubSeries_error_bound (b : ℤ_[p]) (d n : ℕ) :
    ‖PowerSeries.coeff n (inverseOneSubSeries b d-1)‖ ≤ ‖b‖ := by
  cases n with
  | zero => simp [map_sub, inverseOneSubSeries_coeff_zero]
  | succ n =>
    rw [map_sub, PowerSeries.coeff_one, if_neg (by omega), sub_zero]
    apply (rescale_coeff_norm_le b _ (n+1)).trans
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ (norm_nonneg b) (PadicInt.norm_le_one b)) (norm_nonneg b)

end
end CatalanCore.Li2.Port.Li2

end
