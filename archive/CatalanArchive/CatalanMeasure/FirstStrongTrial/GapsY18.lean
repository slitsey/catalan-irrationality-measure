module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkY_18 : ipNoRootCheck AZY (27721250:ℤ) (30583451:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapY_18 : PieceNoRoot AY ((22177 / 40000 : ℚ),(30583451 / 50000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleY hIntY
    (a := 27721250) (b := 30583451) (d := 50000000)
    (by norm_num) (by norm_num) checkY_18
end CatalanMeasure.FirstStrongTrial
