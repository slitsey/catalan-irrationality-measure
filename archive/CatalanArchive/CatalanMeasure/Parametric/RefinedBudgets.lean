module

public import CatalanArchive.CatalanMeasure.Parametric.TwentySharperMain
public import CatalanArchive.CatalanMeasure.Parametric.TwentyFirstCost

@[expose] public section

namespace CatalanMeasure.Parametric

open Real
noncomputable section

/-- Stronger target paid by the exact saved 80-mode trial. -/
def refinedDualTarget : ℝ := 2256215/1000000
def refinedNorm20 : ℝ := 77403691/100000000
def refinedFields20 : ℝ := -254504920/100000000
def refinedMeasureGap : ℝ := refinedDualTarget-Real.log 2/2-
  (8795/4800+(21/200)*Real.log 2)

/-- These are scalar implications; actual field caps are separate certificates. -/
theorem refined_objective_margin :
    refinedNorm20+refinedFields20-(7/10)*Real.log 2 ≤
      -refinedDualTarget-79/250000000 := by
  have hl := Real.log_two_gt_d9
  norm_num [refinedNorm20,refinedFields20,refinedDualTarget] at hl ⊢
  linarith only [hl]

theorem refined_first_constant :
    twentyNorm10+twentyFields10-(7/10)*Real.log 2+refinedDualTarget ≤ -(8/125:ℝ) := by
  have hl := Real.log_two_gt_d9
  norm_num [twentyNorm10,twentyFields10,refinedDualTarget] at hl ⊢
  linarith only [hl]

theorem refined_second_linear :
    (13/5:ℝ)*Real.log 2-refinedFields20+2/25+9/10 < 666/125 := by
  have hu := Real.log_two_lt_d9
  norm_num [refinedFields20] at hu ⊢
  linarith only [hu]

theorem refined_measure_eta_lt : (3655/2000:ℝ) < 400*refinedMeasureGap := by
  have hh := twenty_measure_sharper_eta_lt
  norm_num [refinedMeasureGap,twentyMeasureGap,refinedDualTarget,twentyDualTarget] at hh ⊢
  linarith only [hh]

theorem refined_first_full_interval_budget (a : ℝ) :
    (-(1/5:ℝ)+(8/5)*a-a^2)*Real.log 2+
      twentyNorm10+(1-a)*twentyFields10+a*(1-a)*Real.log 2+
      a*((229193331/100000000:ℝ)/5)+(9/10)*a ≤
        -refinedDualTarget+Real.log 2/2+(269/50)*a := by
  have h0 := refined_first_constant
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have h1 : (13/5:ℝ)*Real.log 2-twentyFields10+
      (229193331/100000000:ℝ)/5+9/10 ≤ (5973/1000:ℝ) := by
    norm_num [twentyFields10] at hu ⊢
    linarith only [hu]
  have hL : (693/1000:ℝ) ≤ Real.log 2 := by
    norm_num at hl ⊢
    linarith only [hl]
  have hquad : -(8/125:ℝ)+(593/1000)*a-(693/500)*a^2 ≤ 0 := by
    nlinarith only [sq_nonneg (a-(593/2772:ℝ))]
  have hsq := mul_le_mul_of_nonneg_right hL (sq_nonneg a)
  by_cases ha : 0 ≤ a
  · have hc := mul_le_mul_of_nonneg_right h1 ha
    nlinarith only [h0,hc,hsq,hquad]
  · have hlo : (27/5:ℝ) ≤ (13/5)*Real.log 2-twentyFields10+
        (229193331/100000000:ℝ)/5+9/10 := by
      norm_num [twentyFields10] at hl ⊢
      linarith only [hl]
    have hc := mul_le_mul_of_nonpos_right hlo (le_of_not_ge ha)
    nlinarith only [h0,hc,hsq,le_of_not_ge ha]

theorem refined_second_grouped_budget {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-(1/5:ℝ)+(8/5)*a-a^2+t-t^2)*Real.log 2+
      refinedNorm20+(1-a)*refinedFields20+a*(1-a)*Real.log 2+
      (a-t)*(2/25:ℝ)+t*(-(63/100:ℝ))+(9/10)*a ≤
        -refinedDualTarget+Real.log 2/2+(107/20)*a := by
  have h0 := refined_objective_margin
  have hu := Real.log_two_lt_d9
  have h1 : (13/5:ℝ)*Real.log 2-refinedFields20+2/25+9/10 ≤ (107/20:ℝ) :=
    refined_second_linear.le.trans (by norm_num)
  have h2 : Real.log 2-(2/25:ℝ)-63/100 ≤ 0 := by
    norm_num at hu ⊢
    linarith only [hu]
  have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc1 := mul_le_mul_of_nonneg_right h1 ha
  have hc2 := mul_nonpos_of_nonpos_of_nonneg h2 ht
  have hs1 := mul_nonneg hL (sq_nonneg a)
  have hs2 := mul_nonneg hL (sq_nonneg t)
  nlinarith only [h0,hc1,hc2,hs1,hs2]

theorem refined_final_scalar_payments :
    (3655/2000:ℝ)+507/2000=2081/1000 ∧
    2 < (4655/538:ℝ) ∧
    1 < 2*(1-(1/1000000:ℝ)*(2*(4655/538)-1)) ∧
    (2081/1000:ℝ) < 2*18 ∧
    (18:ℝ)+4*18*(1/1000000)*(4655/538) < (2081/1000)*(4655/538) ∧
    (538/5:ℝ)*(4655/538)=931 ∧
    3*((538/5:ℝ)*18/(2081/1000)) < 2793 := by norm_num

end
end CatalanMeasure.Parametric
