module

public import CatalanMeasure.Parametric.GroupedMarkedFields
public import CatalanMeasure.Parametric.MixedLogs

/-!
# Canceling marked common factors against the far-sheet weight

The exact marked node weight is a power of 2/(1+x²), on either half interval.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Polynomial Set

noncomputable section

def markedSheetWeight (P : Parameters) (N : ℕ) (x : ℝ) : ℝ :=
  (2 / (1 + x ^ 2)) ^ (P.n N - P.g N - 1)

theorem markedSheetWeight_pos (P : Parameters) (N : ℕ) (x : ℝ) :
    0 < markedSheetWeight P N x := pow_pos (div_pos (by norm_num) (by positivity)) _

theorem log_markedSheetWeight (P : Parameters) (N : ℕ) (x : ℝ) :
    Real.log (markedSheetWeight P N x) =
      ((P.n N - P.g N - 1 : ℕ) : ℝ) * (Real.log 2 - Real.log (1 + x ^ 2)) := by
  rw [markedSheetWeight, Real.log_pow, Real.log_div (by norm_num) (by positivity)]

theorem marked_sheet_weight_cancellation {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    |x| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) * paramRowNodeWeight P N x =
      |(rowCommonFactor P N).eval (realCoordinateInv x)| * markedSheetWeight P N x := by
  have hn := n_pos hP hN
  have hg := two_g_lt_n hP hN
  have hng : P.g N ≤ P.n N := by omega
  have hn1 : 1 ≤ P.n N := by omega
  have hng1 : 1 ≤ P.n N - P.g N := by omega
  have hC1 : 1 ≤ P.C N := by
    rw [C_eq_A_add_residual hP hN]
    omega
  have ht0 : realCoordinateInv x ≠ 0 := by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) hx0) (by positivity)
  have ht1 : realCoordinateInv x ≠ 1 := (sub_pos.mp (one_sub_realCoordinateInv_pos hx)).ne
  have hc0 := rowCommonFactor_eval_ne_zero_of P N ht0 ht1
  have hleft : 0 < |x| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) * paramRowNodeWeight P N x :=
    mul_pos (zpow_pos (abs_pos.mpr hx0) _) (paramRowNodeWeight_pos P N hx hx0)
  have hright : 0 < |(rowCommonFactor P N).eval (realCoordinateInv x)| * markedSheetWeight P N x :=
    mul_pos (abs_pos.mpr hc0) (markedSheetWeight_pos P N x)
  apply Real.log_injOn_pos hleft hright
  rw [Real.log_mul (zpow_ne_zero _ (abs_ne_zero.mpr hx0))
      (paramRowNodeWeight_pos P N hx hx0).ne',
    Real.log_mul (abs_ne_zero.mpr hc0) (markedSheetWeight_pos P N x).ne',
    Real.log_zpow, log_paramRowNodeWeight P N hx hx0,
    commonFactor_coordinate_log_full P N hx hx0, log_markedSheetWeight]
  have hC : (P.C N : ℝ) = (P.A N : ℝ) + (P.n N : ℝ) - (P.g N : ℝ) := by
    rw [C_eq_A_add_residual hP hN, Nat.cast_add, Nat.cast_sub hng]
    ring
  simp only [Int.cast_sub, Int.cast_natCast, Nat.cast_sub hn1,
    Nat.cast_sub hng1, Nat.cast_sub hng, Nat.cast_sub hC1, Nat.cast_one,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [hC]
  ring

theorem twenty_marked_sheet_weight_log {N : ℕ} (hN : 0 < N) (x : ℝ) :
    Real.log (markedSheetWeight twenty N x) =
      (18 * N - 1 : ℝ) * (Real.log 2 - Real.log (1 + x ^ 2)) := by
  rw [log_markedSheetWeight]
  have he : twenty.n N - twenty.g N - 1 = 18 * N - 1 := by
    change 20 * N - 2 * N - 1 = 18 * N - 1
    omega
  rw [he, Nat.cast_sub (by omega : 1 ≤ 18 * N)]
  push_cast
  rfl

end

end CatalanMeasure.Parametric
