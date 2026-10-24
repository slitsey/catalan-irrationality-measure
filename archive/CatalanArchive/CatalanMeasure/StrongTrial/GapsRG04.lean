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
theorem checkRG0_4 : ipNoRootCheck AZR (-9852:ℤ) (-9705:ℤ) (10000:ℤ)=true := by
  certify_hom_gap
theorem gapRG0_4 : PieceNoRoot AR ((-2463 / 2500 : ℚ),(-1941 / 2000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := -9852) (b := -9705) (d := 10000)
    (by norm_num) (by norm_num) checkRG0_4
end CatalanMeasure.StrongTrial
