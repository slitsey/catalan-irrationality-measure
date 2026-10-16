module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_42 : ipNoRootCheck AZX (15318310:ℤ) (16585623:ℤ) (25000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_42 : PieceNoRoot AX ((1531831 / 2500000 : ℚ),(16585623 / 25000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 15318310) (b := 16585623) (d := 25000000)
    (by norm_num) (by norm_num) checkX_42
end CatalanMeasure.FirstStrongTrial
