module

public import CatalanMeasure.G728.NormClosed
public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.NormLogBounds
public import CatalanMeasure.GenD.D58.Cert.Data

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert
open CatalanMeasure.G728 CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem nlV_6 : logUpperOK (((V.drop (2 * 6)).take 2).flatMap (rowTerms V)) (logBsV.getD 6 0) = true := by decide +kernel
theorem nlV_7 : logUpperOK (((V.drop (2 * 7)).take 2).flatMap (rowTerms V)) (logBsV.getD 7 0) = true := by decide +kernel
theorem nlV_8 : logUpperOK (((V.drop (2 * 8)).take 2).flatMap (rowTerms V)) (logBsV.getD 8 0) = true := by decide +kernel
theorem nlV_9 : logUpperOK (((V.drop (2 * 9)).take 2).flatMap (rowTerms V)) (logBsV.getD 9 0) = true := by decide +kernel
theorem nlV_10 : logUpperOK (((V.drop (2 * 10)).take 2).flatMap (rowTerms V)) (logBsV.getD 10 0) = true := by decide +kernel
theorem nlV_11 : logUpperOK (((V.drop (2 * 11)).take 2).flatMap (rowTerms V)) (logBsV.getD 11 0) = true := by decide +kernel
end CatalanMeasure.GenD.D58.Cert
