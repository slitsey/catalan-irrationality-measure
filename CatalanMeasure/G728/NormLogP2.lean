module
public import CatalanMeasure.G728.NormClosed
public import CatalanMeasure.G728.NormLogBounds
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace CatalanMeasure.G728
open CatalanMeasure.Cert OAI.InternalCatalan
theorem nlP_12 : logUpperOK (((P.drop (2 * 12)).take 2).flatMap (rowTerms P)) (logBsP.getD 12 0) = true := by decide +kernel
theorem nlP_13 : logUpperOK (((P.drop (2 * 13)).take 2).flatMap (rowTerms P)) (logBsP.getD 13 0) = true := by decide +kernel
theorem nlP_14 : logUpperOK (((P.drop (2 * 14)).take 2).flatMap (rowTerms P)) (logBsP.getD 14 0) = true := by decide +kernel
theorem nlP_15 : logUpperOK (((P.drop (2 * 15)).take 2).flatMap (rowTerms P)) (logBsP.getD 15 0) = true := by decide +kernel
theorem nlP_16 : logUpperOK (((P.drop (2 * 16)).take 2).flatMap (rowTerms P)) (logBsP.getD 16 0) = true := by decide +kernel
theorem nlP_17 : logUpperOK (((P.drop (2 * 17)).take 2).flatMap (rowTerms P)) (logBsP.getD 17 0) = true := by decide +kernel
end CatalanMeasure.G728
