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
theorem nlP_6 : logUpperOK (((P.drop (2 * 6)).take 2).flatMap (rowTerms P)) (logBsP.getD 6 0) = true := by decide +kernel
theorem nlP_7 : logUpperOK (((P.drop (2 * 7)).take 2).flatMap (rowTerms P)) (logBsP.getD 7 0) = true := by decide +kernel
theorem nlP_8 : logUpperOK (((P.drop (2 * 8)).take 2).flatMap (rowTerms P)) (logBsP.getD 8 0) = true := by decide +kernel
theorem nlP_9 : logUpperOK (((P.drop (2 * 9)).take 2).flatMap (rowTerms P)) (logBsP.getD 9 0) = true := by decide +kernel
theorem nlP_10 : logUpperOK (((P.drop (2 * 10)).take 2).flatMap (rowTerms P)) (logBsP.getD 10 0) = true := by decide +kernel
theorem nlP_11 : logUpperOK (((P.drop (2 * 11)).take 2).flatMap (rowTerms P)) (logBsP.getD 11 0) = true := by decide +kernel
end CatalanMeasure.GenD.D58.Cert
