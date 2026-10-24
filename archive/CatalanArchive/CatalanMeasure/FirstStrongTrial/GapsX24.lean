module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_24 : ipNoRootCheck AZX (0:ℤ) (15195543:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_24 : PieceNoRoot AX ((0 : ℚ),(15195543 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 0) (b := 15195543) (d := 100000000)
    (by norm_num) (by norm_num) checkX_24
end CatalanMeasure.FirstStrongTrial
