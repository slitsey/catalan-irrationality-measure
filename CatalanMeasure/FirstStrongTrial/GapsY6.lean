module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_6 : ipNoRootCheck AZY (15396270:ℤ) (21519511:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_6 : PieceNoRoot AY ((1539627 / 10000000 : ℚ),(21519511 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 15396270) (b := 21519511) (d := 100000000)
    (by norm_num) (by norm_num) checkY_6
end CatalanMeasure.FirstStrongTrial
