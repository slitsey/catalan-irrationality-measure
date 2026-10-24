module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_34 : ipNoRootCheck AZY (92091611:ℤ) (94569351:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_34 : PieceNoRoot AY ((92091611 / 100000000 : ℚ),(94569351 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 92091611) (b := 94569351) (d := 100000000)
    (by norm_num) (by norm_num) checkY_34
end CatalanMeasure.FirstStrongTrial
