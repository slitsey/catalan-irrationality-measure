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
theorem nlV_12 : logUpperOK (((V.drop (2 * 12)).take 2).flatMap (rowTerms V)) (logBsV.getD 12 0) = true := by decide +kernel
theorem nlV_13 : logUpperOK (((V.drop (2 * 13)).take 2).flatMap (rowTerms V)) (logBsV.getD 13 0) = true := by decide +kernel
theorem nlV_14 : logUpperOK (((V.drop (2 * 14)).take 2).flatMap (rowTerms V)) (logBsV.getD 14 0) = true := by decide +kernel
theorem nlV_15 : logUpperOK (((V.drop (2 * 15)).take 2).flatMap (rowTerms V)) (logBsV.getD 15 0) = true := by decide +kernel
theorem nlV_16 : logUpperOK (((V.drop (2 * 16)).take 2).flatMap (rowTerms V)) (logBsV.getD 16 0) = true := by decide +kernel
theorem nlV_17 : logUpperOK (((V.drop (2 * 17)).take 2).flatMap (rowTerms V)) (logBsV.getD 17 0) = true := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
