module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_22 : ipNoRootCheck AZY (67054139:ℤ) (72151320:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_22 : PieceNoRoot AY ((67054139 / 100000000 : ℚ),(1803783 / 2500000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 67054139) (b := 72151320) (d := 100000000)
    (by norm_num) (by norm_num) checkY_22
end CatalanMeasure.FirstStrongTrial
