module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_0 : ipNoRootCheck AZY (0:ℤ) (3274023:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_0 : PieceNoRoot AY ((0 : ℚ),(3274023 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 0) (b := 3274023) (d := 100000000)
    (by norm_num) (by norm_num) checkY_0
end CatalanMeasure.FirstStrongTrial
