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
theorem checkRG1_15 : ipNoRootCheck AZR (999999997622:ℤ) (999999999837:ℤ) (1000000000000:ℤ)=true := by
  certify_hom_gap
theorem gapRG1_15 : PieceNoRoot AR ((499999998811 / 500000000000 : ℚ),(999999999837 / 1000000000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := 999999997622) (b := 999999999837) (d := 1000000000000)
    (by norm_num) (by norm_num) checkRG1_15
end CatalanMeasure.StrongTrial
