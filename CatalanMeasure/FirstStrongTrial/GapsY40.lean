module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_40 : ipNoRootCheck AZY (49017682:ℤ) (49484471:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_40 : PieceNoRoot AY ((24508841 / 25000000 : ℚ),(49484471 / 50000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 49017682) (b := 49484471) (d := 50000000)
    (by norm_num) (by norm_num) checkY_40
end CatalanMeasure.FirstStrongTrial
