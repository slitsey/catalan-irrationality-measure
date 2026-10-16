module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_36 : ipNoRootCheck AZY (94569354:ℤ) (96531579:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_36 : PieceNoRoot AY ((47284677 / 50000000 : ℚ),(96531579 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 94569354) (b := 96531579) (d := 100000000)
    (by norm_num) (by norm_num) checkY_36
end CatalanMeasure.FirstStrongTrial
