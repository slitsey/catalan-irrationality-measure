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
theorem checkRG0_5 : ipNoRootCheck AZR (-1941:ℤ) (-1882:ℤ) (2000:ℤ)=true := by
  certify_hom_gap
theorem gapRG0_5 : PieceNoRoot AR ((-1941 / 2000 : ℚ),(-941 / 1000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := -1941) (b := -1882) (d := 2000)
    (by norm_num) (by norm_num) checkRG0_5
end CatalanMeasure.StrongTrial
