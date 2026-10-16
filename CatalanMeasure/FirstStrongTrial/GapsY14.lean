module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_14 : ipNoRootCheck AZY (42665729:ℤ) (48834505:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_14 : PieceNoRoot AY ((42665729 / 100000000 : ℚ),(9766901 / 20000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 42665729) (b := 48834505) (d := 100000000)
    (by norm_num) (by norm_num) checkY_14
end CatalanMeasure.FirstStrongTrial
