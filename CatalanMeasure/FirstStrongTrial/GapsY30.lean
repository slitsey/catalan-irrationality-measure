module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_30 : ipNoRootCheck AZY (85602413:ℤ) (89044072:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_30 : PieceNoRoot AY ((85602413 / 100000000 : ℚ),(11130509 / 12500000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 85602413) (b := 89044072) (d := 100000000)
    (by norm_num) (by norm_num) checkY_30
end CatalanMeasure.FirstStrongTrial
