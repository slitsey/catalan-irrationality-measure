module

public import OAI.NumberTheory.Catalan.Determinants.RealDeterminantCore
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import OAI.NumberTheory.Catalan.Energy.RealTwoSheetIntegralBound
public import OAI.NumberTheory.Catalan.Estimates.RealEnergyMajorantExponential
public import OAI.NumberTheory.Catalan.FirstBarrier.BarrierCaseOneGlobalBounds
public import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoGlobalBounds
public import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoNorm

@[expose] public section

namespace OAI

noncomputable section
open Set Filter
open scoped BigOperators
namespace InternalCatalan

def realDeterminantCertificateSupBound : ℝ :=
  max (realEnergyDualConstant 1 barrierP1 barrierV1
      (realEnergyRowTrialSup 1 barrierLambda1 barrierP1 barrierV1)
      (realEnergyColumnTrialSup barrierV1))
    (realEnergyDualConstant 2 barrierP2 barrierV2
      (realEnergyRowTrialSup 2 0 barrierP2 barrierV2) (realEnergyColumnTrialSup barrierV2))

theorem realDeterminant_eventually_log_certificate_sup {d : ℝ} (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        realDeterminantCertificateSupBound + d := by
  exact realDeterminant_eventually_log_sup_dual barrier_lambdas.2.1
    barrierP1 barrierV1 barrierP2 barrierV2
    barrier_trials_abs_summable.2.2.1 barrier_trials_abs_summable.2.2.2
    barrier_trials_abs_summable.1 barrier_trials_abs_summable.2.1 hd

end InternalCatalan

end



noncomputable section
open Set Filter

namespace InternalCatalan

private theorem barrier_case2_row_sup_upper :
    realEnergyRowTrialSup 2 0 barrierP2 barrierV2 ≤
      (-98399 / 100000 : ℝ) + 24 / 1000000 := by
  unfold realEnergyRowTrialSup
  refine csSup_le (realEnergyRowTrialField_image_nonempty _ _ _ _) ?_
  rintro y ⟨x, hx, rfl⟩
  simpa [realEnergyRowTrialField, barrierCase2X, barrierLambda2,
    show (2 : ℝ) * 2 = 4 by norm_num] using
    barrierCase2X_global_upper ⟨hx.1.1, hx.1.2, hx.2⟩

private theorem barrier_case2_column_sup_upper :
    realEnergyColumnTrialSup barrierV2 ≤ (-160890 / 100000 : ℝ) + 24 / 1000000 := by
  unfold realEnergyColumnTrialSup
  refine csSup_le (realEnergyColumnTrialField_image_nonempty _) ?_
  rintro y ⟨x, hx, rfl⟩
  simpa only [realEnergyColumnTrialField, barrierCase2Y] using barrierCase2Y_global_upper hx

theorem realDeterminantCaseTwoDual_sharp_lt :
    realEnergyDualConstant 2 barrierP2 barrierV2
      (realEnergyRowTrialSup 2 0 barrierP2 barrierV2)
      (realEnergyColumnTrialSup barrierV2) < -(2290939875 / 1000000000 : ℝ) := by
  unfold realEnergyDualConstant
  nlinarith only [barrier_case2_norm_coarse_upper, barrier_case2_row_sup_upper,
    barrier_case2_column_sup_upper, barrier_two_coarse_total_sharp_lt]

theorem realDeterminantCertificateSupBound_sharp_lt :
    realDeterminantCertificateSupBound < -(2290939875 / 1000000000 : ℝ) := by
  unfold realDeterminantCertificateSupBound
  apply max_lt
  · exact lt_trans realDeterminantCaseOneDual_sharp_lt (by norm_num)
  · exact realDeterminantCaseTwoDual_sharp_lt

theorem realDeterminantCertificateSupBound_lt :
    realDeterminantCertificateSupBound < -(22909 / 10000 : ℝ) :=
  lt_trans realDeterminantCertificateSupBound_sharp_lt (by norm_num)

theorem eventually_realDeterminant_log_upper_sharp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 ≤
        -(2290939875 / 1000000000 : ℝ) + ε := by
  filter_upwards [realDeterminant_eventually_log_certificate_sup hε] with N hN
  intro hnonzero
  linarith only [hN hnonzero, realDeterminantCertificateSupBound_sharp_lt]

theorem eventually_realDeterminant_abs_upper_sharp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, |determinant N| ≤
      Real.exp ((n N : ℝ) ^ 2 *
        (-(2290939875 / 1000000000 : ℝ) + Real.log 2 / 2 + ε)) := by
  filter_upwards [eventually_realDeterminant_log_upper_sharp hε,
    eventually_ge_atTop (1 : ℕ)] with N hN hNpos
  by_cases hz : determinant N = 0
  · rw [hz, abs_zero]
    exact (Real.exp_pos _).le
  have hn : (0 : ℝ) < n N := by
    exact_mod_cast (show 0 < n N by unfold n; omega)
  have hn2 : (0 : ℝ) < (n N : ℝ) ^ 2 := sq_pos_of_pos hn
  have hlog : Real.log |determinant N| ≤ (n N : ℝ) ^ 2 *
      (-(2290939875 / 1000000000 : ℝ) + Real.log 2 / 2 + ε) := by
    have hb : Real.log |determinant N| / (n N : ℝ) ^ 2 ≤
        -(2290939875 / 1000000000 : ℝ) + Real.log 2 / 2 + ε := by
      linarith [hN hz]
    simpa only [mul_comm] using (div_le_iff₀ hn2).mp hb
  calc
    |determinant N| = Real.exp (Real.log |determinant N|) :=
      (Real.exp_log (abs_pos.mpr hz)).symm
    _ ≤ _ := Real.exp_le_exp.mpr hlog

theorem eventually_realDeterminant_log_upper :
    ∀ᶠ N : ℕ in atTop, determinant N ≠ 0 →
      Real.log |determinant N| / (n N : ℝ) ^ 2 - Real.log 2 / 2 <
        -(22909 / 10000 : ℝ) := by
  have hd : 0 < (-(22909 / 10000 : ℝ) - realDeterminantCertificateSupBound) / 2 := by
    linarith [realDeterminantCertificateSupBound_lt]
  filter_upwards [realDeterminant_eventually_log_certificate_sup hd] with N hN
  intro hnonzero
  have hupper := hN hnonzero
  linarith [realDeterminantCertificateSupBound_lt]

end InternalCatalan

end

end OAI
