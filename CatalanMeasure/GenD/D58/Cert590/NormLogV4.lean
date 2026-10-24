module

public import CatalanMeasure.G728.NormClosed
public import CatalanMeasure.GenD.D58.Cert590.NormLogBounds
public import CatalanMeasure.GenD.D58.Cert590.Data

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert590
open CatalanMeasure.G728 CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem nlV_24 : logUpperOK (((V.drop (2 * 24)).take 2).flatMap (rowTerms V)) (logBsV.getD 24 0) = true := by decide +kernel
theorem nlV_25 : logUpperOK (((V.drop (2 * 25)).take 2).flatMap (rowTerms V)) (logBsV.getD 25 0) = true := by decide +kernel
theorem nlV_26 : logUpperOK (((V.drop (2 * 26)).take 2).flatMap (rowTerms V)) (logBsV.getD 26 0) = true := by decide +kernel
theorem nlV_27 : logUpperOK (((V.drop (2 * 27)).take 2).flatMap (rowTerms V)) (logBsV.getD 27 0) = true := by decide +kernel
theorem nlV_28 : logUpperOK (((V.drop (2 * 28)).take 2).flatMap (rowTerms V)) (logBsV.getD 28 0) = true := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
