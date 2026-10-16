module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_15 : ipNoRootCheck AZX (-18321365:ℤ) (-15639292:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_15 : PieceNoRoot AX ((-3664273 / 10000000 : ℚ),(-3909823 / 12500000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -18321365) (b := -15639292) (d := 50000000)
    (by norm_num) (by norm_num) checkX_15
end CatalanMeasure.FirstStrongTrial
