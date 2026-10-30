module

public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section
set_option Elab.async false

/-! The exact numerical contract of the thirds bank (lane B, B4).

`Λ = 7808344448571/2379657280000 + (9/200) log 2`, `D = 251820307144120719543/62500000000000000000`,
`c = 34136273513123893/5000000000000000`; `c / (D - Λ) < 9.52671` (log 2 < 0.6931471808 suffices:
the exponent is 9.5267060080...). -/

namespace CatalanCore.Uniform.Bank.Thirds

/-- The content constant of the thirds route. -/
noncomputable def LamT : ℝ := 7808344448571 / 2379657280000 + 9 / 200 * Real.log 2

def DtT : ℚ := 251820307144120719543 / 62500000000000000000
def ctT : ℚ := 34136273513123893 / 5000000000000000

theorem LamT_lt_Dt : LamT < (DtT : ℝ) := by
  have h := Real.log_two_lt_d9
  unfold LamT DtT
  push_cast
  norm_num at h ⊢
  linarith

theorem LamT_ge : 7808344448571 / 2379657280000 < LamT := by
  have h := Real.log_two_gt_d9
  unfold LamT
  norm_num at h ⊢
  linarith

theorem ratio_le : (ctT : ℝ) / ((DtT : ℝ) - LamT) ≤ ((952671 / 100000 : ℚ) : ℝ) := by
  have h := Real.log_two_lt_d9
  have hl := Real.log_two_gt_d9
  have hpos : 0 < (DtT : ℝ) - LamT := sub_pos.2 LamT_lt_Dt
  rw [div_le_iff₀ hpos]
  unfold LamT DtT ctT
  push_cast
  norm_num at h hl ⊢
  linarith

end CatalanCore.Uniform.Bank.Thirds
