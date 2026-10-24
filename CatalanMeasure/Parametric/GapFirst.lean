module
public import CatalanMeasure.Parametric.GapFinalTransfer
public import CatalanMeasure.Parametric.StrongFirstFields
public import CatalanMeasure.FirstStrongTrial.Sup
@[expose] public section
/-! The first-trial field bounds, shared by the final assemblies. -/
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Filter
noncomputable section

def gapFirstTrial : FirstTrialBoundsAt strongTarget strongFirstCost :=
  strongFirstTrialOfFields FirstStrongTrial.row_sup FirstStrongTrial.column_sup

end
end CatalanMeasure.Parametric
