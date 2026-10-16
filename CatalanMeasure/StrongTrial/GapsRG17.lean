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
theorem checkRG1_7 : ipNoRootCheck AZR (496800000000:ℤ) (499999053041:ℤ) (500000000000:ℤ)=true := by
  certify_hom_gap
theorem gapRG1_7 : PieceNoRoot AR ((621 / 625 : ℚ),(499999053041 / 500000000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := 496800000000) (b := 499999053041) (d := 500000000000)
    (by norm_num) (by norm_num) checkRG1_7
end CatalanMeasure.StrongTrial
