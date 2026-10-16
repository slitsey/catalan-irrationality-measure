module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_32 : ipNoRootCheck AZY (89044075:ℤ) (92091608:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_32 : PieceNoRoot AY ((3561763 / 4000000 : ℚ),(11511451 / 12500000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 89044075) (b := 92091608) (d := 100000000)
    (by norm_num) (by norm_num) checkY_32
end CatalanMeasure.FirstStrongTrial
