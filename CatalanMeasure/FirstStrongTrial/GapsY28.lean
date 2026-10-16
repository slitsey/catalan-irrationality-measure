module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_28 : ipNoRootCheck AZY (81517221:ℤ) (85602410:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_28 : PieceNoRoot AY ((81517221 / 100000000 : ℚ),(8560241 / 10000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 81517221) (b := 85602410) (d := 100000000)
    (by norm_num) (by norm_num) checkY_28
end CatalanMeasure.FirstStrongTrial
