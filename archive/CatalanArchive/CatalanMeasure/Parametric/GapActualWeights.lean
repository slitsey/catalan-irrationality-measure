module
public import CatalanArchive.CatalanMeasure.Parametric.GapWeights
public import CatalanMeasure.GapCircle.Bound
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

theorem gap_actual_weight_joint_le (N k : ℕ) (a : Fin (18*N)) :
    |(rowCommonFactor twenty N).eval (twentyGapNodes N a)| *
      |restrictedWeight twenty N k (twentyGapNodes N) a| ≤
        108000*N*Real.exp (gapWeightCost*N) :=
  gap_weight_joint_le GapCircle.circle_bound N k a

end
end CatalanMeasure.Parametric
