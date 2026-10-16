module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_48 : ipNoRootCheck AZX (75085537:ℤ) (78043533:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_48 : PieceNoRoot AX ((75085537 / 100000000 : ℚ),(78043533 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 75085537) (b := 78043533) (d := 100000000)
    (by norm_num) (by norm_num) checkX_48
end CatalanMeasure.FirstStrongTrial
