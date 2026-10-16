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
theorem checkRG1_0 : ipNoRootCheck AZR (802:ℤ) (2645:ℤ) (5000:ℤ)=true := by
  certify_hom_gap
theorem gapRG1_0 : PieceNoRoot AR ((401 / 2500 : ℚ),(529 / 1000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := 802) (b := 2645) (d := 5000)
    (by norm_num) (by norm_num) checkRG1_0
end CatalanMeasure.StrongTrial
