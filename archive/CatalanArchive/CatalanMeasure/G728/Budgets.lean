module
public import CatalanArchive.CatalanMeasure.Parametric.GapBudgets
@[expose] public section

/-!
# The 728 scalar budgets

Exact rational constants of the 728 programme and the scalar inequalities that
close the energy budgets (retargeted first trial, new second trial) and the final
payments.  Everything here is independent of the trial data.
-/

namespace CatalanMeasure.G728
open CatalanMeasure.Parametric Real
noncomputable section

/-- Target of the 728 programme. -/
def target728 : ℝ := 141027507/62500000
/-- Norm cap of the second trial, `2NP + NV/2`. -/
def normCap728 : ℝ := 24149189/31250000
/-- Field cap of the second trial, `MX + MY`. -/
def fieldCap728 : ℝ := -10176053/4000000
/-- Residual cap of the second trial. -/
def residual728 : ℝ := -5247033/100000000
/-- Near cap of the second trial (unchanged). -/
def nearCap728 : ℝ := -(3/4)
/-- Second cost. -/
def secondCost728 : ℝ := 429033/100000
/-- Radius cost `20 c2 + weight cost`. -/
def rho728 : ℝ := 259299/2500
def kappa728 : ℝ := 1820000/259299
def eta728 : ℝ := 5993/3125
def chi728 : ℝ := 649/1000
def delta728 : ℝ := 1/10000000

/-- Second-trial objective margin at the new caps. -/
theorem objective_margin728 :
    normCap728 + fieldCap728 - (7/10)*Real.log 2 ≤ -target728 - 21/10000000 := by
  have hl := Real.log_two_gt_d9
  norm_num [normCap728, fieldCap728, target728] at hl ⊢
  linarith only [hl]

/-- First-trial budget at the new target (trial and caps unchanged). -/
theorem first_budget728 (a : ℝ) :
    (-(1/5:ℝ)+(8/5)*a-a^2)*Real.log 2+
      strongNormFirst+(1-a)*strongFieldsFirst+a*(1-a)*Real.log 2+
      a*(strongLambda/5)+(9/10)*a ≤
        -target728+Real.log 2/2+(strongFirstCost+9/10)*a := by
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have h0 : strongNormFirst+strongFieldsFirst-(7/10)*Real.log 2+target728 ≤
      -(757/25000:ℝ) := by
    norm_num [strongNormFirst,strongFieldsFirst,target728] at hl ⊢
    linarith only [hl]
  have h1 : (13/5:ℝ)*Real.log 2-strongFieldsFirst+strongLambda/5 ≤
      (46182993841/10000000000:ℝ) := by
    norm_num [strongFieldsFirst,strongLambda] at hu ⊢
    linarith only [hu]
  have h2 : strongFirstCost ≤ (13/5:ℝ)*Real.log 2-strongFieldsFirst+strongLambda/5 := by
    norm_num [strongFirstCost,strongFieldsFirst,strongLambda] at hl ⊢
    linarith only [hl]
  have hs := mul_le_mul_of_nonneg_right hl.le (sq_nonneg a)
  by_cases ha : 0 ≤ a
  · have hc := mul_le_mul_of_nonneg_right h1 ha
    have hquad : -(757/25000:ℝ)+
        (46182993841/10000000000-421/100)*a-(138629436/100000000)*a^2 ≤ 0 := by
      nlinarith only [sq_nonneg (a-
        ((46182993841/10000000000-421/100)/(2*(138629436/100000000)):ℝ))]
    norm_num [strongFirstCost] at h0 hc hs hquad ⊢
    nlinarith only [h0,hc,hs,hquad]
  · have hc := mul_le_mul_of_nonpos_right h2 (le_of_not_ge ha)
    have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hsq := mul_nonneg hL (sq_nonneg a)
    nlinarith only [h0,hc,hsq]

/-- Second-trial budget at the new caps. -/
theorem second_budget728 {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-(1/5:ℝ)+(8/5)*a-a^2+t-t^2)*Real.log 2+
      normCap728+(1-a)*fieldCap728+a*(1-a)*Real.log 2+
      (a-t)*residual728+t*nearCap728+(9/10)*a ≤
        -target728+Real.log 2/2+(secondCost728+9/10)*a := by
  have h0 := objective_margin728
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have h1 : (13/5:ℝ)*Real.log 2-fieldCap728+residual728 ≤
      (42937255901/10000000000:ℝ) := by
    norm_num [fieldCap728,residual728] at hu ⊢
    linarith only [hu]
  have h2 : Real.log 2-residual728+nearCap728 ≤ 0 := by
    norm_num [residual728,nearCap728] at hu ⊢
    linarith only [hu]
  have hc := mul_le_mul_of_nonneg_right h1 ha
  have hs := mul_le_mul_of_nonneg_right hl.le (sq_nonneg a)
  have hq : -(21/10000000:ℝ)+
      (42937255901/10000000000-429033/100000)*a-(138629436/100000000)*a^2 ≤ 0 := by
    nlinarith only [sq_nonneg (a-
      ((42937255901/10000000000-429033/100000)/(2*(138629436/100000000)):ℝ))]
  have htc := mul_nonpos_of_nonpos_of_nonneg h2 ht
  have hts := mul_nonneg (Real.log_nonneg (by norm_num : (1:ℝ)≤2)) (sq_nonneg t)
  norm_num [secondCost728] at hq ⊢
  nlinarith only [h0,hc,hs,hq,htc,hts]

/-- `eta < 400 * measureGapAt target`. -/
theorem eta_lt728 : eta728 < 400*measureGapAt target728 := by
  have hu := Real.log_two_lt_d9
  norm_num [measureGapAt,target728,eta728] at hu ⊢
  linarith only [hu]

theorem chi_eq728 : (507/2000 + 3331/10000 + 624/10000 : ℝ) = chi728 := by
  norm_num [chi728]

/-- All payment arithmetic. -/
theorem payments728 :
    20*strongFirstCost ≤ 20*secondCost728 ∧
    20*secondCost728+gapWeightCost = rho728 ∧
    0 < eta728 + chi728 ∧ 0 < rho728 ∧ 2 < kappa728 ∧ 0 < delta728 ∧
    1 < 2*(1 - delta728*(2*kappa728-1)) ∧
    eta728 + chi728 < 2*18 ∧
    (18:ℝ) + 4*18*delta728*kappa728 < (eta728 + chi728)*kappa728 ∧
    rho728*kappa728 = 728 ∧
    3*rho728*max (18/(eta728 + chi728)) 4 < 2183 := by
  norm_num [strongFirstCost,secondCost728,gapWeightCost,rho728,kappa728,eta728,chi728,delta728]

end
end CatalanMeasure.G728
