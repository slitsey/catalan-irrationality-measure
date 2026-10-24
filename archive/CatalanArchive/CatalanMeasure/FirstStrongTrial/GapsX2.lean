module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_2 : ipNoRootCheck AZX (-99998879:ℤ) (-99574000:ℤ) (100000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_2 : PieceNoRoot AX ((-99998879 / 100000000 : ℚ),(-49787 / 50000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -99998879) (b := -99574000) (d := 100000000)
    (by norm_num) (by norm_num) checkX_2
end CatalanMeasure.FirstStrongTrial
