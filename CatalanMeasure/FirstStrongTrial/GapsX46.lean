module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_46 : ipNoRootCheck AZX (35335466:ℤ) (37542767:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_46 : PieceNoRoot AX ((17667733 / 25000000 : ℚ),(37542767 / 50000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 35335466) (b := 37542767) (d := 50000000)
    (by norm_num) (by norm_num) checkX_46
end CatalanMeasure.FirstStrongTrial
