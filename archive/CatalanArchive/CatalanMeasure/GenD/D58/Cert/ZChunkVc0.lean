module

public import CatalanArchive.CatalanMeasure.GenD.D58.Cert.ZDefs

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert
open CatalanMeasure.G728 CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem uVcN_c0 : uClenN ((Vc.reverse).take 40) ([], []) = uVcN1 := by decide +kernel
end CatalanMeasure.GenD.D58.Cert
