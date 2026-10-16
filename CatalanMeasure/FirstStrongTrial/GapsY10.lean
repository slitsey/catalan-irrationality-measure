module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_10 : ipNoRootCheck AZY (29126771:ℤ) (35484322:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_10 : PieceNoRoot AY ((29126771 / 100000000 : ℚ),(17742161 / 50000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 29126771) (b := 35484322) (d := 100000000)
    (by norm_num) (by norm_num) checkY_10
end CatalanMeasure.FirstStrongTrial
