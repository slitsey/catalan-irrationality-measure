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
theorem checkRG0_0 : ipNoRootCheck AZR (-1000000000000:ℤ) (-999999801557:ℤ) (1000000000000:ℤ)=true := by
  certify_hom_gap
theorem gapRG0_0 : PieceNoRoot AR ((-1 : ℚ),(-999999801557 / 1000000000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := -1000000000000) (b := -999999801557) (d := 1000000000000)
    (by norm_num) (by norm_num) checkRG0_0
end CatalanMeasure.StrongTrial
