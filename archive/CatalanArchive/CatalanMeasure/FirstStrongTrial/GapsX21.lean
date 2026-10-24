module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_21 : ipNoRootCheck AZX (-19630304:ℤ) (-15306479:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_21 : PieceNoRoot AX ((-613447 / 3125000 : ℚ),(-15306479 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -19630304) (b := -15306479) (d := 100000000)
    (by norm_num) (by norm_num) checkX_21
end CatalanMeasure.FirstStrongTrial
