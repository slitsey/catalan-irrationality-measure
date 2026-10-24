module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_13 : ipNoRootCheck AZX (-41823970:ℤ) (-36642733:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_13 : PieceNoRoot AX ((-4182397 / 10000000 : ℚ),(-36642733 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -41823970) (b := -36642733) (d := 100000000)
    (by norm_num) (by norm_num) checkX_13
end CatalanMeasure.FirstStrongTrial
