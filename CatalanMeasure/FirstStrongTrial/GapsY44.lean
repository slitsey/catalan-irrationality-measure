module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_44 : ipNoRootCheck AZY (99606468:ℤ) (99831853:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_44 : PieceNoRoot AY ((24901617 / 25000000 : ℚ),(99831853 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 99606468) (b := 99831853) (d := 100000000)
    (by norm_num) (by norm_num) checkY_44
end CatalanMeasure.FirstStrongTrial
