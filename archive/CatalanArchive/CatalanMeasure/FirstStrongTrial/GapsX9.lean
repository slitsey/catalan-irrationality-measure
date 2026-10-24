module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_9 : ipNoRootCheck AZX (-72800000:ℤ) (-45596901:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_9 : PieceNoRoot AX ((-91 / 125 : ℚ),(-45596901 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -72800000) (b := -45596901) (d := 100000000)
    (by norm_num) (by norm_num) checkX_9
end CatalanMeasure.FirstStrongTrial
