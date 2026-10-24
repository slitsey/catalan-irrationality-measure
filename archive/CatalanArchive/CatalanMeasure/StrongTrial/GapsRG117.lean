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
theorem checkRG1_17 : ipNoRootCheck AZR (6249999999:ℤ) (6250000000:ℤ) (6250000000:ℤ)=true := by
  certify_hom_gap
theorem gapRG1_17 : PieceNoRoot AR ((6249999999 / 6250000000 : ℚ),(1 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := 6249999999) (b := 6250000000) (d := 6250000000)
    (by norm_num) (by norm_num) checkRG1_17
end CatalanMeasure.StrongTrial
