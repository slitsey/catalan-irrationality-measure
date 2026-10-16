module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# A uniform near-residual field cap from two elementary logarithm inequalities
-/

@[expose] public section

namespace CatalanMeasure.Parametric

noncomputable section

theorem near_residual_field_le {p y : ℝ} (hp : 9 / 50 ≤ p)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    -(9 / 10 : ℝ) * Real.log (1 + y ^ 2) + (4 / 5) * Real.log y - p * y ≤
      -(63 / 100 : ℝ) := by
  have hd : 0 < 1 + y ^ 2 := by positivity
  have hl := Real.one_sub_inv_le_log_of_pos hd
  have hu := Real.log_le_sub_one_of_pos hy
  have hpy := mul_le_mul_of_nonneg_right hp hy.le
  have hquad : 0 ≤ (62 / 100 : ℝ) * y ^ 2 - (45 / 100) * y + 17 / 100 := by
    nlinarith only [sq_nonneg (y - (45 / 124 : ℝ))]
  have hfactor := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy1) hquad
  have hid : (4 / 5 : ℝ) * (y - 1) - (9 / 50 : ℝ) * y -
      (9 / 10 : ℝ) * (1 - (1 + y ^ 2)⁻¹) + 63 / 100 =
      (y - 1) * ((62 / 100 : ℝ) * y ^ 2 - (45 / 100) * y + 17 / 100) /
        (1 + y ^ 2) := by
    field_simp
    ring
  have hrat := div_nonpos_of_nonpos_of_nonneg hfactor hd.le
  rw [← hid] at hrat
  linarith only [hl, hu, hpy, hrat]

end

end CatalanMeasure.Parametric
