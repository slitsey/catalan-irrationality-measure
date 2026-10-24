module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_8 : ipNoRootCheck AZY (10759757:ℤ) (14563384:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_8 : PieceNoRoot AY ((10759757 / 50000000 : ℚ),(1820423 / 6250000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 10759757) (b := 14563384) (d := 50000000)
    (by norm_num) (by norm_num) checkY_8
end CatalanMeasure.FirstStrongTrial
