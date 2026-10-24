module

public import CatalanArchive.CatalanMeasure.Parametric.TwentyBudgets

/-!
# Grouped population budgets reusing the published trial constants

These are scalar budget implications. The actual grouped field bounds and
the original determinant assembly are separate obligations.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

noncomputable section

theorem published_first_full_interval_budget (a : ℝ) :
    (-(1 / 5 : ℝ) + (8 / 5) * a - a ^ 2) * Real.log 2 +
      twentyNorm10 + (1 - a) * twentyFields10 + a * (1 - a) * Real.log 2 +
      a * ((229193331 / 100000000 : ℝ) / 5) + (9 / 10) * a ≤
        -twentyDualTarget + Real.log 2 / 2 + (27 / 5) * a := by
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have h0 : twentyNorm10 + twentyFields10 - (7 / 10 : ℝ) * Real.log 2 +
      twentyDualTarget ≤ -(8 / 125 : ℝ) := by
    dsimp only [twentyNorm10, twentyFields10, twentyDualTarget]
    norm_num at hl ⊢
    linarith only [hl]
  have h1 : (13 / 5 : ℝ) * Real.log 2 - twentyFields10 +
      (229193331 / 100000000 : ℝ) / 5 + 9 / 10 ≤ (5973 / 1000 : ℝ) := by
    dsimp only [twentyFields10]
    norm_num at hu ⊢
    linarith only [hu]
  have hL : (693 / 1000 : ℝ) ≤ Real.log 2 := by
    norm_num at hl ⊢
    linarith only [hl]
  -- The discriminant is negative: the whole quadratic is below zero.
  have hquad : -(8 / 125 : ℝ) + (573 / 1000) * a - (693 / 500) * a ^ 2 ≤ 0 := by
    nlinarith only [sq_nonneg (a - (191 / 924 : ℝ))]
  have hsq := mul_le_mul_of_nonneg_right hL (sq_nonneg a)
  by_cases ha : 0 ≤ a
  · have hc := mul_le_mul_of_nonneg_right h1 ha
    nlinarith only [h0, hc, hsq, hquad]
  · -- For negative a, use the actual linear coefficient's lower bound.
    have hlo : (27 / 5 : ℝ) ≤ (13 / 5 : ℝ) * Real.log 2 - twentyFields10 +
        (229193331 / 100000000 : ℝ) / 5 + 9 / 10 := by
      dsimp only [twentyFields10]
      norm_num at hl ⊢
      linarith only [hl]
    have hc := mul_le_mul_of_nonpos_right hlo (le_of_not_ge ha)
    nlinarith only [h0, hc, hsq]

theorem published_second_grouped_budget {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-(1 / 5 : ℝ) + (8 / 5) * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      twentyNorm20 + (1 - a) * twentyFields20 + a * (1 - a) * Real.log 2 +
      (a - t) * (2 / 25 : ℝ) + t * (-(63 / 100 : ℝ)) + (9 / 10) * a ≤
        -twentyDualTarget + Real.log 2 / 2 + (107 / 20) * a := by
  have h0 := twenty_budget_checks.2.1
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have h1 : (13 / 5 : ℝ) * Real.log 2 - twentyFields20 + 2 / 25 + 9 / 10 ≤
      (107 / 20 : ℝ) := by
    dsimp only [twentyFields20]
    norm_num at hu ⊢
    linarith only [hu]
  have h2 : Real.log 2 - (2 / 25 : ℝ) - 63 / 100 ≤ 0 := by
    norm_num at hu ⊢
    linarith only [hu]
  have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc1 := mul_le_mul_of_nonneg_right h1 ha
  have hc2 := mul_nonpos_of_nonpos_of_nonneg h2 ht
  have hs1 := mul_nonneg hL (sq_nonneg a)
  have hs2 := mul_nonneg hL (sq_nonneg t)
  nlinarith only [h0, hc1, hc2, hs1, hs2]

end

end CatalanMeasure.Parametric
