module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_5 : ipNoRootCheck AZX (-983:ℤ) (-966:ℤ) (1000:ℤ)=true := by
  certify_hom_gap
theorem gapX_5 : PieceNoRoot AX ((-983 / 1000 : ℚ),(-483 / 500 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -983) (b := -966) (d := 1000)
    (by norm_num) (by norm_num) checkX_5
end CatalanMeasure.FirstStrongTrial
