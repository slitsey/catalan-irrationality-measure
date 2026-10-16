module
public import CatalanMeasure.Parametric.GapFinalTransfer
public import CatalanMeasure.Parametric.GapActualWeights
public import CatalanMeasure.FirstStrongTrial.Sup
public import CatalanMeasure.StrongTrial.Sup
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Filter
open scoped Topology
noncomputable section

def gapFirstTrial : FirstTrialBoundsAt strongTarget strongFirstCost :=
  strongFirstTrialOfFields FirstStrongTrial.row_sup FirstStrongTrial.column_sup

def gapSecondTrial :
    SecondTrialBoundsOn strongTarget gapResidualCap (-(3/4:ℝ)) gapSecondCost gapAtomDomain :=
  gapSecondTrialOfFields StrongTrial.row_sup StrongTrial.column_sup (by
    intro x hx hg
    have hgap : (StrongTrial.residualGap:ℝ) ≤ |x| := by
      simpa only [StrongTrial.residualGap,physicalAtomGap] using hg
    have hh := StrongTrial.residual_gap_sup x hx hgap
    convert hh using 1 <;> norm_num [StrongTrial.gapResidualM,gapResidualCap])

theorem gap_weight_bounds : GapWeightBounds :=
  Filter.Eventually.of_forall fun N k a => gap_actual_weight_joint_le N k a

theorem catalan_irrationalityMeasure_878 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b:ℝ)^(-(878:ℝ))< |catalan-(a:ℝ)/b| :=
  measure_878_of_gap_bounds gapFirstTrial gapSecondTrial gap_weight_bounds

theorem catalan_irrationalityMeasure_2632 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b:ℝ)^(-(2632:ℝ))< |catalan-(a:ℝ)/b| :=
  measure_2632_of_gap_bounds gapFirstTrial gapSecondTrial gap_weight_bounds

end
end CatalanMeasure.Parametric
