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
theorem checkRG1_6 : ipNoRootCheck AZR (617:ℤ) (621:ℤ) (625:ℤ)=true := by
  certify_hom_gap
theorem gapRG1_6 : PieceNoRoot AR ((617 / 625 : ℚ),(621 / 625 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := 617) (b := 621) (d := 625)
    (by norm_num) (by norm_num) checkRG1_6
end CatalanMeasure.StrongTrial
