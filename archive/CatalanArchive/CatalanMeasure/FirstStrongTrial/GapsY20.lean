module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_20 : ipNoRootCheck AZY (61166905:ℤ) (67054136:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_20 : PieceNoRoot AY ((12233381 / 20000000 : ℚ),(8381767 / 12500000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 61166905) (b := 67054136) (d := 100000000)
    (by norm_num) (by norm_num) checkY_20
end CatalanMeasure.FirstStrongTrial
