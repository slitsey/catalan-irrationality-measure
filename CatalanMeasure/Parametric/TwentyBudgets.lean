module
public import CatalanMeasure.Parametric.PopulationMissingMass
public import Mathlib.Analysis.Complex.ExponentialBounds
@[expose] public section
namespace CatalanMeasure.Parametric
noncomputable section

def twentyDualTarget : ℝ :=2256085/1000000
def twentyNorm10 : ℝ :=39057323/40000000
def twentyNorm11 : ℝ :=10072013/10000000
def twentyNorm20 : ℝ :=77403499/100000000
def twentyNorm21 : ℝ :=159606223/200000000
def twentyFields10 : ℝ :=-2811609/1000000
def twentyFields11 : ℝ :=-2413331/1000000
def twentyFields20 : ℝ :=-508987/200000
def twentyFields21 : ℝ :=-10567/5000
def twentyFixed10 : ℝ :=-(2/5)*Real.log 2+(1/5)*(229193331/100000000)
def twentyFixed11 : ℝ :=-(2/5)*Real.log 2+(1/5)*(120853833/50000000)
def twentyFirstCost : ℝ :=twentyNorm11-twentyNorm10+twentyFields11-2*twentyFields10+
  twentyFixed10+2*Real.log 2
def twentyFirstQuadratic : ℝ :=twentyFields10-twentyFields11+twentyFixed11-twentyFixed10-Real.log 2
def twentySecondCost : ℝ :=twentyNorm21-twentyNorm20+twentyFields21-2*twentyFields20-
  1/5+2*Real.log 2
def twentySecondQuadratic : ℝ :=twentyFields20-twentyFields21-Real.log 2

/-- These are algebraic budget checks, not assertions that the concrete fields satisfy them. -/
theorem twenty_budget_checks :
    twentyNorm10+twentyFields10-(7/10)*Real.log 2 ≤ -twentyDualTarget-8/125 ∧
    twentyNorm20+twentyFields20-(7/10)*Real.log 2 ≤ -twentyDualTarget ∧
    twentyFirstCost ≤ 481/100 ∧ twentyFirstQuadratic ≤ -(53/50) ∧
    twentySecondCost ≤ 43/10 ∧ twentySecondQuadratic ≤ 0 :=by
  have hl :=Real.log_two_gt_d9
  have hu :=Real.log_two_lt_d9
  dsimp only [twentyNorm10,twentyNorm11,twentyNorm20,twentyNorm21,twentyFields10,twentyFields11,
    twentyFields20,twentyFields21,twentyDualTarget,twentyFirstCost,twentyFirstQuadratic,
    twentySecondCost,twentySecondQuadratic,twentyFixed10,twentyFixed11]
  norm_num at hl hu ⊢
  constructor
  · linarith only [hl]
  constructor
  · linarith only [hl]
  constructor
  · linarith only [hu]
  constructor
  · linarith only [hl]
  constructor
  · linarith only [hu]
  · linarith only [hl]

/-- The proposed arithmetic cost leaves a strictly positive eta margin. Its
    actual denominator bound is a separate required proof. -/
theorem twenty_eta_budget : (177/100:ℝ)<400*(twentyDualTarget-Real.log 2/2-
    (2937/1600+(21/200)*Real.log 2-1/300)) :=by
  have hu :=Real.log_two_lt_d9
  unfold twentyDualTarget
  norm_num at hu ⊢
  linarith only [hu]

theorem twenty_rho_budget : (33:ℝ)+20*(43/10)<120 :=by norm_num

end
end CatalanMeasure.Parametric
