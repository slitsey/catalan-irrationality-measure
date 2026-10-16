module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_50 : ipNoRootCheck AZX (4877721:ℤ) (6250000:ℤ) (6250000:ℤ)=true := by
  certify_hom_gap
theorem gapX_50 : PieceNoRoot AX ((4877721 / 6250000 : ℚ),(1 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 4877721) (b := 6250000) (d := 6250000)
    (by norm_num) (by norm_num) checkX_50
end CatalanMeasure.FirstStrongTrial
