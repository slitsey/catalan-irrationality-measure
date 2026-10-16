module

public import CatalanMeasure.Parametric.TwentyGroupedTrialBounds
public import CatalanMeasure.Parametric.FullIntervalFormula

/-!
# Exact common-factor cancellation and finite-size near-field control

The residual exponent is 16N-1. Its logarithmic coefficient is uniformly at least
3/4 for N positive, so the near-field cap does not omit an unbounded correction
at nodes close to zero.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan Polynomial Set

noncomputable section

theorem commonFactor_coordinate_log_full (P : Parameters) (N : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    Real.log |(rowCommonFactor P N).eval (realCoordinateInv x)| =
      (P.A N : ℝ) * (Real.log 2 + Real.log |x| - Real.log (1 + x ^ 2)) +
      (P.h N : ℝ) * (2 * Real.log (1 - x) - Real.log (1 + x ^ 2)) := by
  have hd : 0 < 1 + x ^ 2 := by positivity
  have hm : 0 < 1 - x := sub_pos.mpr hx.2
  have ht0 : realCoordinateInv x ≠ 0 := by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) hx0) hd.ne'
  have h1t := one_sub_realCoordinateInv_pos hx
  have hlogt : Real.log |realCoordinateInv x| =
      Real.log 2 + Real.log |x| - Real.log (1 + x ^ 2) := by
    rw [realCoordinateInv, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos hd, Real.log_div (mul_ne_zero (by norm_num) (abs_ne_zero.mpr hx0)) hd.ne',
      Real.log_mul (by norm_num) (abs_ne_zero.mpr hx0)]
  have he : 1 - realCoordinateInv x = (1 - x) ^ 2 / (1 + x ^ 2) := by
    unfold realCoordinateInv
    field_simp
    ring
  have hlogone : Real.log (1 - realCoordinateInv x) =
      2 * Real.log (1 - x) - Real.log (1 + x ^ 2) := by
    rw [he, Real.log_div (pow_ne_zero _ hm.ne') hd.ne', Real.log_pow]
    norm_num
  simp only [rowCommonFactor, eval_mul, eval_pow, eval_X, eval_sub, eval_one, abs_mul, abs_pow]
  rw [abs_of_pos h1t, Real.log_mul (pow_ne_zero _ (abs_ne_zero.mpr ht0))
    (pow_ne_zero _ h1t.ne'), Real.log_pow, Real.log_pow, hlogt, hlogone]

theorem population_row_field_sub_common_full {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) (k : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    paramPopulationRowField P N k x -
      Real.log |(rowCommonFactor P N).eval (realCoordinateInv x)| / (P.n N : ℝ) =
      -(P.A N : ℝ) / (P.n N : ℝ) * Real.log 2 -
        (k / 2 - (P.g N : ℝ) / (P.n N : ℝ)) * Real.log (1 + x ^ 2) := by
  have hn : (P.n N : ℝ) ≠ 0 := by exact_mod_cast (n_pos hP hN).ne'
  have hg : P.g N ≤ P.n N := by have := two_g_lt_n hP hN; omega
  have hH : (P.H N : ℝ) =
      (P.A N : ℝ) + (P.n N : ℝ) - (P.g N : ℝ) + (P.h N : ℝ) := by
    change ((P.C N + P.h N : ℕ) : ℝ) = _
    rw [C_eq_A_add_residual hP hN, Nat.cast_add, Nat.cast_add, Nat.cast_sub hg]
    ring
  rw [commonFactor_coordinate_log_full P N hx hx0]
  unfold paramPopulationRowField
  rw [hH]
  field_simp
  ring

theorem near_residual_field_le_three_quarters {p y : ℝ} (hp : 9 / 50 ≤ p)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    -(9 / 10 : ℝ) * Real.log (1 + y ^ 2) + (3 / 4) * Real.log y - p * y ≤
      -(63 / 100 : ℝ) := by
  have hd : 0 < 1 + y ^ 2 := by positivity
  have hl := Real.one_sub_inv_le_log_of_pos hd
  have hu := Real.log_le_sub_one_of_pos hy
  have hpy := mul_le_mul_of_nonneg_right hp hy.le
  have hquad : 0 ≤ (57 / 100 : ℝ) * y ^ 2 - (45 / 100) * y + 12 / 100 := by
    nlinarith only [sq_nonneg (y - (15 / 38 : ℝ))]
  have hfactor := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy1) hquad
  have hid : (3 / 4 : ℝ) * (y - 1) - (9 / 50 : ℝ) * y -
      (9 / 10 : ℝ) * (1 - (1 + y ^ 2)⁻¹) + 63 / 100 =
      (y - 1) * ((57 / 100 : ℝ) * y ^ 2 - (45 / 100) * y + 12 / 100) /
        (1 + y ^ 2) := by
    field_simp
    ring
  have hrat := div_nonpos_of_nonpos_of_nonneg hfactor hd.le
  rw [← hid] at hrat
  linarith only [hl, hu, hpy, hrat]

theorem twenty_finite_near_field_bound {N : ℕ} (hN : 0 < N) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    -(9 / 10 : ℝ) * Real.log (1 + y ^ 2) +
      ((16 * N - 1 : ℕ) : ℝ) / (20 * N) * Real.log y -
        TwentyCertified.p20 1 * y ≤ -(63 / 100 : ℝ) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : (0 : ℝ) < 20 * N := by positivity
  have hc : (3 / 4 : ℝ) ≤ ((16 * N - 1 : ℕ) : ℝ) / (20 * N) := by
    rw [le_div_iff₀ hd, Nat.cast_sub (by omega : 1 ≤ 16 * N)]
    push_cast
    linarith only [hn]
  have hl : Real.log y ≤ 0 := Real.log_nonpos hy.1.le hy.2.le
  have hm := mul_le_mul_of_nonpos_right hc hl
  have hb := near_residual_field_le_three_quarters TwentyCertified.p20_first_lower hy.1 hy.2.le
  linarith only [hm, hb]

theorem twenty_field_ratios {N : ℕ} (hN : 0 < N) :
    (twenty.A N : ℝ) / (twenty.n N : ℝ) = 2 / 5 ∧
      (twenty.g N : ℝ) / (twenty.n N : ℝ) = 1 / 10 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  constructor
  · rw [twenty_A]
    change ((8 * N : ℕ) : ℝ) / ((20 * N : ℕ) : ℝ) = _
    push_cast
    field_simp
    ring
  · change ((2 * N : ℕ) : ℝ) / ((20 * N : ℕ) : ℝ) = _
    push_cast
    field_simp
    ring

theorem twenty_marked_actual_field_after_common {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    paramPopulationRowField twenty N 2 x -
      Real.log |(rowCommonFactor twenty N).eval (realCoordinateInv x)| / (twenty.n N : ℝ) -
        2 * barrierTrialT TwentyCertified.p20 x ≤
      -(2 / 5 : ℝ) * Real.log 2 + 2 / 25 := by
  have he := population_row_field_sub_common_full twenty_admissible hN 2 hx hx0
  rw [neg_div, (twenty_field_ratios hN).1, (twenty_field_ratios hN).2] at he
  have hb := TwentyCertified.grouped_marked_field_bound ⟨hx.1.le, hx.2.le⟩
  norm_num only at he
  linarith only [he, hb]

theorem twenty_marked_near_field_after_common {N : ℕ} (hN : 0 < N) {y : ℝ}
    (hy : y ∈ Ioo (0 : ℝ) 1) :
    paramPopulationRowField twenty N 2 y -
      Real.log |(rowCommonFactor twenty N).eval (realCoordinateInv y)| / (twenty.n N : ℝ) +
        ((16 * N - 1 : ℕ) : ℝ) / (twenty.n N : ℝ) * Real.log y -
          TwentyCertified.p20 1 * y ≤ -(2 / 5 : ℝ) * Real.log 2 - 63 / 100 := by
  have hy' : y ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have he := population_row_field_sub_common_full twenty_admissible hN 2 hy' hy.1.ne'
  rw [neg_div, (twenty_field_ratios hN).1, (twenty_field_ratios hN).2] at he
  have hb := twenty_finite_near_field_bound hN hy
  norm_num only at he
  have hnu : (twenty.n N : ℝ) = 20 * N := by simp [Parameters.n, twenty]
  rw [hnu] at he ⊢
  linarith only [he, hb]

theorem twenty_marked_first_field_after_common {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    paramPopulationRowField twenty N 1 x + lambda * paramCaseField twenty N x -
      Real.log |(rowCommonFactor twenty N).eval (realCoordinateInv x)| / (twenty.n N : ℝ) ≤
        -(2 / 5 : ℝ) * Real.log 2 + lambda / 5 := by
  have he := population_row_field_sub_common_full twenty_admissible hN 1 hx hx0
  have hb := paramResidualFixedOne_le twenty_admissible hN hlambda x
  rw [neg_div, (twenty_field_ratios hN).1, (twenty_field_ratios hN).2] at he
  have hr : lambda * 2 * (twenty.g N : ℝ) / (twenty.n N : ℝ) = lambda / 5 := by
    calc
      _ = 2 * lambda * ((twenty.g N : ℝ) / (twenty.n N : ℝ)) := by ring
      _ = _ := by rw [(twenty_field_ratios hN).2]; ring
  rw [neg_div, (twenty_field_ratios hN).1, hr] at hb
  unfold paramResidualFixedOne at hb
  rw [neg_div, (twenty_field_ratios hN).1, (twenty_field_ratios hN).2] at hb
  norm_num only at he
  linarith only [he, hb]

end

end CatalanMeasure.Parametric
