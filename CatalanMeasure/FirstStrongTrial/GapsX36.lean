module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_36 : ipNoRootCheck AZX (22281572:ℤ) (25267575:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_36 : PieceNoRoot AX ((5570393 / 12500000 : ℚ),(1010703 / 2000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 22281572) (b := 25267575) (d := 50000000)
    (by norm_num) (by norm_num) checkX_36
end CatalanMeasure.FirstStrongTrial
