module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_26 : ipNoRootCheck AZX (7597773:ℤ) (9854610:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_26 : PieceNoRoot AX ((7597773 / 50000000 : ℚ),(985461 / 5000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 7597773) (b := 9854610) (d := 50000000)
    (by norm_num) (by norm_num) checkX_26
end CatalanMeasure.FirstStrongTrial
