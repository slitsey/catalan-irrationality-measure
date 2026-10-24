module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_12 : ipNoRootCheck AZY (35484325:ℤ) (42665726:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_12 : PieceNoRoot AY ((1419373 / 4000000 : ℚ),(21332863 / 50000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 35484325) (b := 42665726) (d := 100000000)
    (by norm_num) (by norm_num) checkY_12
end CatalanMeasure.FirstStrongTrial
