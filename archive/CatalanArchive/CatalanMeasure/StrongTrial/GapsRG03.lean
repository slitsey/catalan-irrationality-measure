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
theorem checkRG0_3 : ipNoRootCheck AZR (-4963:ℤ) (-4926:ℤ) (5000:ℤ)=true := by
  certify_hom_gap
theorem gapRG0_3 : PieceNoRoot AR ((-4963 / 5000 : ℚ),(-2463 / 2500 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := -4963) (b := -4926) (d := 5000)
    (by norm_num) (by norm_num) checkRG0_3
end CatalanMeasure.StrongTrial
