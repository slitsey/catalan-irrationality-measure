module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_42 : ipNoRootCheck AZY (19793789:ℤ) (19921293:ℤ) (20000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_42 : PieceNoRoot AY ((19793789 / 20000000 : ℚ),(19921293 / 20000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 19793789) (b := 19921293) (d := 20000000)
    (by norm_num) (by norm_num) checkY_42
end CatalanMeasure.FirstStrongTrial
