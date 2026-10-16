module
public import CatalanMeasure.StrongTrial.GapResidualFoundations
public meta import CatalanMeasure.StrongTrial.ResidualData
public import CatalanMeasure.Cert.HomWitness
public import CatalanMeasure.StrongTrial.Foundations
public import CatalanMeasure.Cert.MarkedResidualClosed
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkRG1_11 : ipNoRootCheck AZR (999999723984:ℤ) (999999974091:ℤ) (1000000000000:ℤ)=true := by
  certify_hom_gap
theorem gapRG1_11 : PieceNoRoot AR ((62499982749 / 62500000000 : ℚ),(999999974091 / 1000000000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := 999999723984) (b := 999999974091) (d := 1000000000000)
    (by norm_num) (by norm_num) checkRG1_11
end CatalanMeasure.StrongTrial
