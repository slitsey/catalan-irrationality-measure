module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_28 : ipNoRootCheck AZX (19709223:ℤ) (26838009:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_28 : PieceNoRoot AX ((19709223 / 100000000 : ℚ),(26838009 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 19709223) (b := 26838009) (d := 100000000)
    (by norm_num) (by norm_num) checkX_28
end CatalanMeasure.FirstStrongTrial
