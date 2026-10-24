module

public import CatalanMeasure.GenD.D58.Cert.ZDefs

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert
open CatalanMeasure.G728 CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem uPcN_c2 : uClenN ((((Pc.reverse).drop 40).drop 40).take 40) uPcN2 = uPcN3 := by decide +kernel
end CatalanMeasure.GenD.D58.Cert
