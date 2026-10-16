module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_38 : ipNoRootCheck AZY (96531582:ℤ) (98035361:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_38 : PieceNoRoot AY ((48265791 / 50000000 : ℚ),(98035361 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 96531582) (b := 98035361) (d := 100000000)
    (by norm_num) (by norm_num) checkY_38
end CatalanMeasure.FirstStrongTrial
