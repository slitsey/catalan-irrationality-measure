module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_4 : ipNoRootCheck AZY (7708335:ℤ) (15396267:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_4 : PieceNoRoot AY ((1541667 / 20000000 : ℚ),(15396267 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 7708335) (b := 15396267) (d := 100000000)
    (by norm_num) (by norm_num) checkY_4
end CatalanMeasure.FirstStrongTrial
