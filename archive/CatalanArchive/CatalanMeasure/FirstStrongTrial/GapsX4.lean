module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_4 : ipNoRootCheck AZX (-1983:ℤ) (-1966:ℤ) (2000:ℤ)=true := by
  certify_hom_gap
theorem gapX_4 : PieceNoRoot AX ((-1983 / 2000 : ℚ),(-983 / 1000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -1983) (b := -1966) (d := 2000)
    (by norm_num) (by norm_num) checkX_4
end CatalanMeasure.FirstStrongTrial
