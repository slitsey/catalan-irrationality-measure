module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_38 : ipNoRootCheck AZX (50535153:ℤ) (56025827:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_38 : PieceNoRoot AX ((50535153 / 100000000 : ℚ),(56025827 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 50535153) (b := 56025827) (d := 100000000)
    (by norm_num) (by norm_num) checkX_38
end CatalanMeasure.FirstStrongTrial
