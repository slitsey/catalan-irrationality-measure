module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_44 : ipNoRootCheck AZX (66342495:ℤ) (70670929:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_44 : PieceNoRoot AX ((13268499 / 20000000 : ℚ),(70670929 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 66342495) (b := 70670929) (d := 100000000)
    (by norm_num) (by norm_num) checkX_44
end CatalanMeasure.FirstStrongTrial
