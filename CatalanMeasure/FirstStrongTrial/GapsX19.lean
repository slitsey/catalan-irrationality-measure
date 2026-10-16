module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_19 : ipNoRootCheck AZX (-26167222:ℤ) (-19630307:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_19 : PieceNoRoot AX ((-13083611 / 50000000 : ℚ),(-19630307 / 100000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -26167222) (b := -19630307) (d := 100000000)
    (by norm_num) (by norm_num) checkX_19
end CatalanMeasure.FirstStrongTrial
