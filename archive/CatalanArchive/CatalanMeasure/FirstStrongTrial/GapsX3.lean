module
public import CatalanArchive.CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_3 : ipNoRootCheck AZX (-49787:ℤ) (-49575:ℤ) (50000:ℤ)=true := by
  certify_hom_gap
theorem gapX_3 : PieceNoRoot AX ((-49787 / 50000 : ℚ),(-1983 / 2000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := -49787) (b := -49575) (d := 50000)
    (by norm_num) (by norm_num) checkX_3
end CatalanMeasure.FirstStrongTrial
