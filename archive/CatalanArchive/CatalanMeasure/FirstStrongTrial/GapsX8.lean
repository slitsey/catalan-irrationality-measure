module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_8 : ipNoRootCheck AZX (-108:ℤ) (-91:ℤ) (125:ℤ)=true := by
  certify_hom_gap
theorem gapX_8 : PieceNoRoot AX ((-108 / 125 : ℚ),(-91 / 125 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -108) (b := -91) (d := 125)
    (by norm_num) (by norm_num) checkX_8
end CatalanMeasure.FirstStrongTrial
