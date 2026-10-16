module
public import CatalanMeasure.Parametric.StrongBudgets
@[expose] public section
namespace CatalanMeasure.Parametric
open Real
noncomputable section

def physicalAtomGap : ℚ := 401/2500
def interpolationGap : ℚ := 2005000/6410801
def gapResidualCap : ℝ := -131/2500
def gapSecondCost : ℝ := 13421/3125
def gapWeightCost : ℝ := 17913/1000
def gapRadiusCost : ℝ := 519037/5000

theorem atom_gap_parameters :
    0<physicalAtomGap ∧ physicalAtomGap<1 ∧
    2*physicalAtomGap/(1+physicalAtomGap^2)=interpolationGap := by
  norm_num [physicalAtomGap,interpolationGap]

theorem gap_second_budget {a t : ℝ} (ha : 0≤a) (ht : 0≤t) :
    (-(1/5:ℝ)+(8/5)*a-a^2+t-t^2)*Real.log 2+
      strongNormSecond+(1-a)*strongFieldsSecond+a*(1-a)*Real.log 2+
      (a-t)*gapResidualCap+t*(-(3/4:ℝ))+(9/10)*a ≤
        -strongTarget+Real.log 2/2+(gapSecondCost+9/10)*a := by
  have h0 := strong_objective_margin
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  have h1 : (13/5:ℝ)*Real.log 2-strongFieldsSecond+gapResidualCap ≤
      (21475830653/5000000000:ℝ) := by
    norm_num [strongFieldsSecond,gapResidualCap] at hu ⊢
    linarith only [hu]
  have h2 : Real.log 2-gapResidualCap-3/4 ≤ 0 := by
    norm_num [gapResidualCap] at hu ⊢
    linarith only [hu]
  have hc := mul_le_mul_of_nonneg_right h1 ha
  have hs := mul_le_mul_of_nonneg_right hl.le (sq_nonneg a)
  have hq : -(9/250000000:ℝ)+
      (21475830653/5000000000-13421/3125)*a-(138629436/100000000)*a^2 ≤ 0 := by
    nlinarith only [sq_nonneg (a-
      ((21475830653/5000000000-13421/3125)/(2*(138629436/100000000)):ℝ))]
  have htc := mul_nonpos_of_nonpos_of_nonneg h2 ht
  have hts := mul_nonneg (Real.log_nonneg (by norm_num : (1:ℝ)≤2)) (sq_nonneg t)
  norm_num [gapSecondCost] at hq ⊢
  nlinarith only [h0,hc,hs,hq,htc,hts]

theorem gap_final_payments :
    20*strongFirstCost ≤ 20*gapSecondCost ∧
    20*gapSecondCost+gapWeightCost=gapRadiusCost ∧
    (375279/200000:ℝ)+507/2000=425979/200000 ∧
    2<(4390000/519037:ℝ) ∧
    1<2*(1-(1/10000000:ℝ)*(2*(4390000/519037)-1)) ∧
    (425979/200000:ℝ)<2*18 ∧
    (18:ℝ)+4*18*(1/10000000)*(4390000/519037)<(425979/200000)*(4390000/519037) ∧
    gapRadiusCost*(4390000/519037)=878 ∧
    3*gapRadiusCost*max (18/(425979/200000)) 4<2632 := by
  norm_num [strongFirstCost,gapSecondCost,gapWeightCost,gapRadiusCost]

end
end CatalanMeasure.Parametric
