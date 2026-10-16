module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_11 : ipNoRootCheck AZX (-45596898:ℤ) (-41823973:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_11 : PieceNoRoot AX ((-22798449 / 50000000 : ℚ),(-41823973 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -45596898) (b := -41823973) (d := 100000000)
    (by norm_num) (by norm_num) checkX_11
end CatalanMeasure.FirstStrongTrial
