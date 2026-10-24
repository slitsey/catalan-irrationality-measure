module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_16 : ipNoRootCheck AZY (48834508:ℤ) (55442497:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_16 : PieceNoRoot AY ((12208627 / 25000000 : ℚ),(55442497 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 48834508) (b := 55442497) (d := 100000000)
    (by norm_num) (by norm_num) checkY_16
end CatalanMeasure.FirstStrongTrial
