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
theorem checkRG0_10 : ipNoRootCheck AZR (-66820880127:ℤ) (-20050000000:ℤ) (125000000000:ℤ)=true := by
  certify_hom_gap
theorem gapRG0_10 : PieceNoRoot AR ((-66820880127 / 125000000000 : ℚ),(-401 / 2500 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := -66820880127) (b := -20050000000) (d := 125000000000)
    (by norm_num) (by norm_num) checkRG0_10
end CatalanMeasure.StrongTrial
