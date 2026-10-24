module
public import CatalanMeasure.G728.NormClosed
public import CatalanArchive.CatalanMeasure.G728.NormLogBounds
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
namespace CatalanMeasure.G728
open CatalanMeasure.Cert OAI.InternalCatalan
theorem nlV_23 : logUpperOK (((V.drop (2 * 23)).take 2).flatMap (rowTerms V)) (logBsV.getD 23 0) = true := by decide +kernel
theorem nlV_24 : logUpperOK (((V.drop (2 * 24)).take 2).flatMap (rowTerms V)) (logBsV.getD 24 0) = true := by decide +kernel
theorem nlV_25 : logUpperOK (((V.drop (2 * 25)).take 2).flatMap (rowTerms V)) (logBsV.getD 25 0) = true := by decide +kernel
theorem nlV_26 : logUpperOK (((V.drop (2 * 26)).take 2).flatMap (rowTerms V)) (logBsV.getD 26 0) = true := by decide +kernel
theorem nlV_27 : logUpperOK (((V.drop (2 * 27)).take 2).flatMap (rowTerms V)) (logBsV.getD 27 0) = true := by decide +kernel
end CatalanMeasure.G728
