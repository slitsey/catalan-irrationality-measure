module
public import CatalanMeasure.FirstStrongTrial.Foundations
public meta import CatalanMeasure.FirstStrongTrial.FieldsData
public import CatalanMeasure.Cert.HomWitness
@[expose] public section
namespace CatalanMeasure.FirstStrongTrial
open CatalanMeasure.Cert
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem checkX_30 : ipNoRootCheck AZX (13419006:ℤ) (16156385:ℤ) (50000000:ℤ)=true := by
  certify_hom_gap
theorem gapX_30 : PieceNoRoot AX ((6709503 / 25000000 : ℚ),(3231277 / 10000000 : ℚ),false) := by
  intro _
  exact noRoot_of_integer_check hScaleX hIntX
    (a := 13419006) (b := 16156385) (d := 50000000)
    (by norm_num) (by norm_num) checkX_30
end CatalanMeasure.FirstStrongTrial
