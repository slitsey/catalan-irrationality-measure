module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_23 : ipNoRootCheck AZX (-3826619:ℤ) (0:ℤ) (25000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_23 : PieceNoRoot AX ((-3826619 / 25000000 : ℚ),(0 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -3826619) (b := 0) (d := 25000000)
    (by norm_num) (by norm_num) checkX_23
end CatalanMeasure.FirstStrongTrial
