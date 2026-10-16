module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_46 : ipNoRootCheck AZY (6239491:ℤ) (6250000:ℤ) (6250000:ℤ)=true := by
  certify_hom_gap
theorem gapY_46 : PieceNoRoot AY ((6239491 / 6250000 : ℚ),(1 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 6239491) (b := 6250000) (d := 6250000)
    (by norm_num) (by norm_num) checkY_46
end CatalanMeasure.FirstStrongTrial
