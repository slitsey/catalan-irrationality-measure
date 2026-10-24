module

public import CatalanMeasure.G728.NormClosed
public import CatalanMeasure.GenD.D58.Cert.NormLogBounds
public import CatalanMeasure.GenD.D58.Cert.Data

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert
open CatalanMeasure.G728 CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem nlV_18 : logUpperOK (((V.drop (2 * 18)).take 2).flatMap (rowTerms V)) (logBsV.getD 18 0) = true := by decide +kernel
theorem nlV_19 : logUpperOK (((V.drop (2 * 19)).take 2).flatMap (rowTerms V)) (logBsV.getD 19 0) = true := by decide +kernel
theorem nlV_20 : logUpperOK (((V.drop (2 * 20)).take 2).flatMap (rowTerms V)) (logBsV.getD 20 0) = true := by decide +kernel
theorem nlV_21 : logUpperOK (((V.drop (2 * 21)).take 2).flatMap (rowTerms V)) (logBsV.getD 21 0) = true := by decide +kernel
theorem nlV_22 : logUpperOK (((V.drop (2 * 22)).take 2).flatMap (rowTerms V)) (logBsV.getD 22 0) = true := by decide +kernel
end CatalanMeasure.GenD.D58.Cert
