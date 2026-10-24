module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_6 : ipNoRootCheck AZX (-483:ℤ) (-466:ℤ) (500:ℤ)=true := by
  certify_hom_gap
theorem gapX_6 : PieceNoRoot AX ((-483 / 500 : ℚ),(-233 / 250 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -483) (b := -466) (d := 500)
    (by norm_num) (by norm_num) checkX_6
end CatalanMeasure.FirstStrongTrial
