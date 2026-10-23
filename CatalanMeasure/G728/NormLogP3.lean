module
public import CatalanMeasure.G728.NormClosed
public import CatalanMeasure.G728.NormLogBounds
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace CatalanMeasure.G728
open CatalanMeasure.Cert OAI.InternalCatalan
theorem nlP_18 : logUpperOK (((P.drop (2 * 18)).take 2).flatMap (rowTerms P)) (logBsP.getD 18 0) = true := by decide +kernel
theorem nlP_19 : logUpperOK (((P.drop (2 * 19)).take 2).flatMap (rowTerms P)) (logBsP.getD 19 0) = true := by decide +kernel
theorem nlP_20 : logUpperOK (((P.drop (2 * 20)).take 2).flatMap (rowTerms P)) (logBsP.getD 20 0) = true := by decide +kernel
theorem nlP_21 : logUpperOK (((P.drop (2 * 21)).take 2).flatMap (rowTerms P)) (logBsP.getD 21 0) = true := by decide +kernel
theorem nlP_22 : logUpperOK (((P.drop (2 * 22)).take 2).flatMap (rowTerms P)) (logBsP.getD 22 0) = true := by decide +kernel
end CatalanMeasure.G728
