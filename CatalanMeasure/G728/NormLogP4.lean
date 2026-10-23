module
public import CatalanMeasure.G728.NormClosed
public import CatalanMeasure.G728.NormLogBounds
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace CatalanMeasure.G728
open CatalanMeasure.Cert OAI.InternalCatalan
theorem nlP_23 : logUpperOK (((P.drop (2 * 23)).take 2).flatMap (rowTerms P)) (logBsP.getD 23 0) = true := by decide +kernel
theorem nlP_24 : logUpperOK (((P.drop (2 * 24)).take 2).flatMap (rowTerms P)) (logBsP.getD 24 0) = true := by decide +kernel
theorem nlP_25 : logUpperOK (((P.drop (2 * 25)).take 2).flatMap (rowTerms P)) (logBsP.getD 25 0) = true := by decide +kernel
theorem nlP_26 : logUpperOK (((P.drop (2 * 26)).take 2).flatMap (rowTerms P)) (logBsP.getD 26 0) = true := by decide +kernel
theorem nlP_27 : logUpperOK (((P.drop (2 * 27)).take 2).flatMap (rowTerms P)) (logBsP.getD 27 0) = true := by decide +kernel
end CatalanMeasure.G728
