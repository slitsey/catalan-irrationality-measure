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
theorem checkRG1_4 : ipNoRootCheck AZR (1898:ℤ) (1949:ℤ) (2000:ℤ)=true := by
  certify_hom_gap
theorem gapRG1_4 : PieceNoRoot AR ((949 / 1000 : ℚ),(1949 / 2000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleR hIntR (a := 1898) (b := 1949) (d := 2000)
    (by norm_num) (by norm_num) checkRG1_4
end CatalanMeasure.StrongTrial
