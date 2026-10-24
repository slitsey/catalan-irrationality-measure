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
theorem checkRG1_3 : ipNoRootCheck AZR (224265267381:ℤ) (237250000000:ℤ) (250000000000:ℤ)=true := by
  certify_hom_gap
theorem gapRG1_3 : PieceNoRoot AR ((224265267381 / 250000000000 : ℚ),(949 / 1000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := 224265267381) (b := 237250000000) (d := 250000000000)
    (by norm_num) (by norm_num) checkRG1_3
end CatalanMeasure.StrongTrial
