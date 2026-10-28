module
public import CatalanCore.Uniform.Decay.Nodes.EnergyGeom
@[expose] public section

/-!
# `O(r log r)` bound for the error terms of `energy_geom`

`Err_le`: the explicit error `Err` of `BlockGeom.energy_geom` is at most `A r (1 + log (1+r))`
with an explicit constant `A` depending only on the block data and the certificate constants.
`eventually_le_sq`: hence `Err ≤ δ r²` for large `r` (any `δ > 0`).
-/

namespace CatalanCore.Uniform
open Decay.Nodes Finset CatalanLambda.Decay

theorem log_one_add_le_sqrt (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ 2 * Real.sqrt x := by
  have h1 : Real.log (1 + x) = 2 * Real.log (Real.sqrt (1 + x)) := by
    rw [← Real.log_rpow (Real.sqrt_pos.mpr (by linarith))]
    rw [show (Real.sqrt (1 + x)) ^ (2 : ℝ) = 1 + x by
      rw [Real.rpow_two]; exact Real.sq_sqrt (by linarith)]
  have h2 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (show 0 < 1 + x by linarith))
  have h3 : Real.sqrt (1 + x) ≤ 1 + Real.sqrt x := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]
  linarith

/-- `A r (1 + log (1+r)) ≤ δ r²` for large `r`. -/
theorem eventually_le_sq (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ R0 : ℕ, ∀ r : ℕ, R0 ≤ r → A * r * (1 + Real.log (1 + r)) ≤ δ * (r : ℝ) ^ 2 := by
  obtain ⟨R0, hR0⟩ := exists_nat_ge ((3 * A / δ) ^ 2 + 1)
  refine ⟨R0, fun r hr => ?_⟩
  have hr1 : (1 : ℝ) ≤ r := by
    have : (1 : ℝ) ≤ (R0 : ℝ) := by
      have : 0 ≤ (3 * A / δ) ^ 2 := sq_nonneg _
      linarith
    exact this.trans (by exact_mod_cast hr)
  have hrr : (R0 : ℝ) ≤ r := by exact_mod_cast hr
  have hlog := log_one_add_le_sqrt (r : ℝ) (by linarith)
  have hs : 3 * A / δ ≤ Real.sqrt r :=
    (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))
  have hsr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt r := by
    rw [Real.one_le_sqrt]; exact hr1
  have h3 : 3 * A ≤ δ * Real.sqrt r := by
    have := mul_le_mul_of_nonneg_left hs hδ.le
    rwa [mul_div_cancel₀ _ hδ.ne'] at this
  have hrr0 : (0 : ℝ) ≤ r := by linarith
  have hAr : 0 ≤ A * (r : ℝ) := mul_nonneg hA hrr0
  have ha : A * r * (1 + Real.log (1 + r)) ≤ A * r * (1 + 2 * Real.sqrt r) :=
    mul_le_mul_of_nonneg_left (by linarith) hAr
  have hb : A * r * (1 + 2 * Real.sqrt r) ≤ A * r * (3 * Real.sqrt r) :=
    mul_le_mul_of_nonneg_left (by linarith) hAr
  have hc : 3 * A * (r * Real.sqrt r) ≤ δ * Real.sqrt r * (r * Real.sqrt r) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have hd : δ * Real.sqrt r * (r * Real.sqrt r) = δ * (r : ℝ) ^ 2 := by
    have : δ * Real.sqrt r * (r * Real.sqrt r) = δ * r * (Real.sqrt r * Real.sqrt r) := by ring
    rw [this, hsr]; ring
  calc A * r * (1 + Real.log (1 + r)) ≤ A * r * (3 * Real.sqrt r) := ha.trans hb
    _ = 3 * A * (r * Real.sqrt r) := by ring
    _ ≤ δ * (r : ℝ) ^ 2 := hc.trans hd.le

end CatalanCore.Uniform
