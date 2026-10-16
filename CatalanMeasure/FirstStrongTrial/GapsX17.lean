module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_17 : ipNoRootCheck AZX (-31278581:ℤ) (-26167225:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_17 : PieceNoRoot AX ((-31278581 / 100000000 : ℚ),(-1046689 / 4000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -31278581) (b := -26167225) (d := 100000000)
    (by norm_num) (by norm_num) checkX_17
end CatalanMeasure.FirstStrongTrial
