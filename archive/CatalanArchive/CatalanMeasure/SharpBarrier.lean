module

public import OAI.NumberTheory.Catalan.Determinants.RealDeterminantUpper
public import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoGlobalBounds
public import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoNorm
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# OpenAI's second-barrier certificate, read to seven digits

OpenAI's certificate for the energy dual in the second case evaluates the row and column
trial fields at the left ends of brackets around their stationary points to about `10⁻¹¹`,
but records the results only as `< -0.98399` and `< -1.60890`, and rounds the norm term up to
`0.77844`.  The fields equioscillate: their largest bracket values are `-0.98403339` and
`-1.60894641`.  The point files now record `< -0.9840333` and `< -1.6089463`
(`barrierCase2X_global_upper_sharp`, `barrierCase2Y_global_upper_sharp`); the sharp rational
norm bound `48651467 / 62500000` is OpenAI's.  Together these move OpenAI's constant
`2.290939875` to `2.2910468`, nearly doubling the gap `γ = U - A`.

The first case is unchanged: its certified value `-2.296789875` is already below `-2.2910468`.
-/

open Filter

namespace OAI.InternalCatalan

theorem sharpBarrier_case2_row_sup_upper :
    realEnergyRowTrialSup 2 0 barrierP2 barrierV2 ≤
      (-9840333 / 10000000 : ℝ) + 24 / 1000000 := by
  unfold realEnergyRowTrialSup
  refine csSup_le (realEnergyRowTrialField_image_nonempty _ _ _ _) ?_
  rintro y ⟨x, hx, rfl⟩
  simpa [realEnergyRowTrialField, barrierCase2X, barrierLambda2,
    show (2 : ℝ) * 2 = 4 by norm_num] using
    barrierCase2X_global_upper_sharp ⟨hx.1.1, hx.1.2, hx.2⟩

theorem sharpBarrier_case2_column_sup_upper :
    realEnergyColumnTrialSup barrierV2 ≤ (-16089463 / 10000000 : ℝ) + 24 / 1000000 := by
  unfold realEnergyColumnTrialSup
  refine csSup_le (realEnergyColumnTrialField_image_nonempty _) ?_
  rintro y ⟨x, hx, rfl⟩
  simpa only [realEnergyColumnTrialField, barrierCase2Y] using
    barrierCase2Y_global_upper_sharp hx

theorem sharpBarrier_total_lt :
    -(11 / 16 : ℝ) * Real.log 2 + 48651467 / 62500000 - 9840333 / 10000000 -
      16089463 / 10000000 + 48 / 1000000 < -(22910468 / 10000000 : ℝ) := by
  have := Real.log_two_gt_d9
  norm_num at this ⊢
  linarith

theorem sharpBarrier_caseTwoDual_lt :
    realEnergyDualConstant 2 barrierP2 barrierV2
      (realEnergyRowTrialSup 2 0 barrierP2 barrierV2)
      (realEnergyColumnTrialSup barrierV2) < -(22910468 / 10000000 : ℝ) := by
  unfold realEnergyDualConstant
  nlinarith only [barrier_case2_norm_rational_upper, sharpBarrier_case2_row_sup_upper,
    sharpBarrier_case2_column_sup_upper, sharpBarrier_total_lt]

theorem sharpBarrier_certificateSupBound_lt :
    realDeterminantCertificateSupBound < -(22910468 / 10000000 : ℝ) := by
  unfold realDeterminantCertificateSupBound
  apply max_lt
  · exact lt_trans realDeterminantCaseOneDual_sharp_lt (by norm_num)
  · exact sharpBarrier_caseTwoDual_lt

/-- OpenAI's upper bound for `|Δ_N(G)|`, with the constant `U = 2.2910468`. -/
theorem eventually_realDeterminant_abs_upper_sharper {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, |determinant N| ≤
      Real.exp ((n N : ℝ) ^ 2 *
        (-(22910468 / 10000000 : ℝ) + Real.log 2 / 2 + ε)) := by
  filter_upwards [realDeterminant_eventually_log_certificate_sup hε,
    eventually_ge_atTop (1 : ℕ)] with N hN hNpos
  by_cases hz : determinant N = 0
  · rw [hz, abs_zero]
    exact (Real.exp_pos _).le
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hn2 : (0 : ℝ) < (n N : ℝ) ^ 2 := sq_pos_of_pos hn
  have hlog : Real.log |determinant N| ≤ (n N : ℝ) ^ 2 *
      (-(22910468 / 10000000 : ℝ) + Real.log 2 / 2 + ε) := by
    have hb : Real.log |determinant N| / (n N : ℝ) ^ 2 ≤
        -(22910468 / 10000000 : ℝ) + Real.log 2 / 2 + ε := by
      linarith [hN hz, sharpBarrier_certificateSupBound_lt]
    simpa only [mul_comm] using (div_le_iff₀ hn2).mp hb
  calc
    |determinant N| = Real.exp (Real.log |determinant N|) :=
      (Real.exp_log (abs_pos.mpr hz)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

end OAI.InternalCatalan
