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
theorem checkRG1_5 : ipNoRootCheck AZR (9745:ℤ) (9872:ℤ) (10000:ℤ)=true := by
  certify_hom_gap
theorem gapRG1_5 : PieceNoRoot AR ((1949 / 2000 : ℚ),(617 / 625 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := 9745) (b := 9872) (d := 10000)
    (by norm_num) (by norm_num) checkRG1_5
end CatalanMeasure.StrongTrial
