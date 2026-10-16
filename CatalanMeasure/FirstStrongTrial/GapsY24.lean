module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_24 : ipNoRootCheck AZY (72151323:ℤ) (77189757:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_24 : PieceNoRoot AY ((72151323 / 100000000 : ℚ),(77189757 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 72151323) (b := 77189757) (d := 100000000)
    (by norm_num) (by norm_num) checkY_24
end CatalanMeasure.FirstStrongTrial
