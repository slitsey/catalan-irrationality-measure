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
theorem checkRG0_2 : ipNoRootCheck AZR (-499999900777:ℤ) (-496300000000:ℤ) (500000000000:ℤ)=true := by
  certify_hom_gap
theorem gapRG0_2 : PieceNoRoot AR ((-499999900777 / 500000000000 : ℚ),(-4963 / 5000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := -499999900777) (b := -496300000000) (d := 500000000000)
    (by norm_num) (by norm_num) checkRG0_2
end CatalanMeasure.StrongTrial
