module
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum
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

end
end CatalanMeasure.Parametric
