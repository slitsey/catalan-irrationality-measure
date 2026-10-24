module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_7 : ipNoRootCheck AZX (-233:ℤ) (-216:ℤ) (250:ℤ)=true := by
  certify_hom_gap
theorem gapX_7 : PieceNoRoot AX ((-233 / 250 : ℚ),(-108 / 125 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -233) (b := -216) (d := 250)
    (by norm_num) (by norm_num) checkX_7
end CatalanMeasure.FirstStrongTrial
