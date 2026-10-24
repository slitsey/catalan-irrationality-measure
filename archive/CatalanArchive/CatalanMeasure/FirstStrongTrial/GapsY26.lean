module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_26 : ipNoRootCheck AZY (38594880:ℤ) (40758609:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_26 : PieceNoRoot AY ((120609 / 156250 : ℚ),(40758609 / 50000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 38594880) (b := 40758609) (d := 50000000)
    (by norm_num) (by norm_num) checkY_26
end CatalanMeasure.FirstStrongTrial
