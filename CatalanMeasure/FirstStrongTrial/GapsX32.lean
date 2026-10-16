module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_32 : ipNoRootCheck AZX (32312773:ℤ) (38897196:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_32 : PieceNoRoot AX ((32312773 / 100000000 : ℚ),(9724299 / 25000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 32312773) (b := 38897196) (d := 100000000)
    (by norm_num) (by norm_num) checkX_32
end CatalanMeasure.FirstStrongTrial
