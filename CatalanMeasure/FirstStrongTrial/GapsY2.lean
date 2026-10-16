module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_2 : ipNoRootCheck AZY (1637013:ℤ) (3854166:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_2 : PieceNoRoot AY ((1637013 / 50000000 : ℚ),(1927083 / 25000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 1637013) (b := 3854166) (d := 50000000)
    (by norm_num) (by norm_num) checkY_2
end CatalanMeasure.FirstStrongTrial
