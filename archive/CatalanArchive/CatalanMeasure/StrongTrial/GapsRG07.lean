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
theorem checkRG0_7 : ipNoRootCheck AZR (-883:ℤ) (-767:ℤ) (1000:ℤ)=true := by
  certify_hom_gap
theorem gapRG0_7 : PieceNoRoot AR ((-883 / 1000 : ℚ),(-767 / 1000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := -883) (b := -767) (d := 1000)
    (by norm_num) (by norm_num) checkRG0_7
end CatalanMeasure.StrongTrial
