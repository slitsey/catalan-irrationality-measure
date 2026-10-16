module
public import CatalanMeasure.Parametric.TargetSmallness
@[expose] public section
namespace CatalanMeasure.Parametric
open Real
noncomputable section

def strongTarget : ℝ := 22563367/10000000
def strongNormFirst : ℝ := 67761/100000
def strongFieldsFirst : ℝ := -247913/100000
def strongLambda : ℝ := 168493357/100000000
def strongNormSecond : ℝ := 3096999/4000000
def strongFieldsSecond : ℝ := -127269173/50000000
def strongResidual : ℝ := 7207/200000
def strongFirstCost : ℝ := 421/100
def strongSecondCost : ℝ := 109579/25000

theorem strong_objective_margin :
    strongNormSecond+strongFieldsSecond-(7/10)*Real.log 2 ≤
      -strongTarget-9/250000000 := by
  have hl := Real.log_two_gt_d9
  norm_num [strongNormSecond,strongFieldsSecond,strongTarget] at hl ⊢
  linarith only [hl]

theorem strong_first_budget (a : ℝ) :
    (-(1/5:ℝ)+(8/5)*a-a^2)*Real.log 2+
      strongNormFirst+(1-a)*strongFieldsFirst+a*(1-a)*Real.log 2+
      a*(strongLambda/5)+(9/10)*a ≤
        -strongTarget+Real.log 2/2+(strongFirstCost+9/10)*a := by
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have h0 : strongNormFirst+strongFieldsFirst-(7/10)*Real.log 2+strongTarget ≤
      -(15193163/500000000:ℝ) := by
    norm_num [strongNormFirst,strongFieldsFirst,strongTarget] at hl ⊢
    linarith only [hl]
  have h1 : (13/5:ℝ)*Real.log 2-strongFieldsFirst+strongLambda/5 ≤
      (23091496923/5000000000:ℝ) := by
    norm_num [strongFieldsFirst,strongLambda] at hu ⊢
    linarith only [hu]
  have h2 : strongFirstCost ≤ (13/5:ℝ)*Real.log 2-strongFieldsFirst+strongLambda/5 := by
    norm_num [strongFirstCost,strongFieldsFirst,strongLambda] at hl ⊢
    linarith only [hl]
  have hs := mul_le_mul_of_nonneg_right hl.le (sq_nonneg a)
  by_cases ha : 0 ≤ a
  · have hc := mul_le_mul_of_nonneg_right h1 ha
    have hquad : -(15193163/500000000:ℝ)+
        (23091496923/5000000000-421/100)*a-(138629436/100000000)*a^2 ≤ 0 := by
      nlinarith only [sq_nonneg (a-
        ((23091496923/5000000000-421/100)/(2*(138629436/100000000)):ℝ))]
    norm_num [strongFirstCost] at h0 hc hs hquad ⊢
    nlinarith only [h0,hc,hs,hquad]
  · have hc := mul_le_mul_of_nonpos_right h2 (le_of_not_ge ha)
    have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hsq := mul_nonneg hL (sq_nonneg a)
    nlinarith only [h0,hc,hsq]

theorem strong_second_budget {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-(1/5:ℝ)+(8/5)*a-a^2+t-t^2)*Real.log 2+
      strongNormSecond+(1-a)*strongFieldsSecond+a*(1-a)*Real.log 2+
      (a-t)*strongResidual+t*(-(3/4:ℝ))+(9/10)*a ≤
        -strongTarget+Real.log 2/2+(strongSecondCost+9/10)*a := by
  have h0 := strong_objective_margin
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have h1 : (13/5:ℝ)*Real.log 2-strongFieldsSecond+strongResidual ≤
      (21918005653/5000000000:ℝ) := by
    norm_num [strongFieldsSecond,strongResidual] at hu ⊢
    linarith only [hu]
  have h2 : Real.log 2-strongResidual-3/4 ≤ 0 := by
    norm_num [strongResidual] at hu ⊢
    linarith only [hu]
  have hc := mul_le_mul_of_nonneg_right h1 ha
  have hs := mul_le_mul_of_nonneg_right hl.le (sq_nonneg a)
  have hq : -(9/250000000:ℝ)+
      (21918005653/5000000000-109579/25000)*a-(138629436/100000000)*a^2 ≤ 0 := by
    nlinarith only [sq_nonneg (a-
      ((21918005653/5000000000-109579/25000)/(2*(138629436/100000000)):ℝ))]
  have htc := mul_nonpos_of_nonpos_of_nonneg h2 ht
  have hts := mul_nonneg (Real.log_nonneg (by norm_num : (1:ℝ)≤2)) (sq_nonneg t)
  norm_num [strongSecondCost] at hq ⊢
  nlinarith only [h0,hc,hs,hq,htc,hts]

theorem strong_eta_lt : (375279/200000:ℝ) < 400*measureGapAt strongTarget := by
  have hu := Real.log_two_lt_d9
  norm_num [measureGapAt,strongTarget] at hu ⊢
  linarith only [hu]

end
end CatalanMeasure.Parametric
