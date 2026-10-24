module
public import CatalanArchive.CatalanMeasure.StrongTrial.GapResidualFoundations
public meta import CatalanArchive.CatalanMeasure.StrongTrial.ResidualData
public import CatalanMeasure.Cert.HomWitness
public import CatalanArchive.CatalanMeasure.StrongTrial.Foundations
public import CatalanArchive.CatalanMeasure.Cert.MarkedResidualClosed
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkRG1_1 : ipNoRootCheck AZR (529000000000:ℤ) (897061069521:ℤ) (1000000000000:ℤ)=true := by
  certify_hom_gap
theorem gapRG1_1 : PieceNoRoot AR ((529 / 1000 : ℚ),(897061069521 / 1000000000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := 529000000000) (b := 897061069521) (d := 1000000000000)
    (by norm_num) (by norm_num) checkRG1_1
end CatalanMeasure.StrongTrial
