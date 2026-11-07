module

public import CatalanMeasure.GenD.DesignInstance.PositiveCert.ZDefs
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.ZChunkPc0
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.ZChunkPc1
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.ZChunkPc2
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.ZChunkPc3

@[expose] public section

namespace CatalanMeasure.GenD.D58.Cert590
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
theorem uPcN_end : uClenN (((((Pc.reverse).drop 40).drop 40).drop 40).drop 40) uPcN4 = uPcN4 := by decide +kernel
theorem uClenN_Pc : uClenN Pc.reverse ([], []) = uPcN4 :=
  uClenN_chain (Pc.reverse) 40 uPcN_c0 (uClenN_chain ((Pc.reverse).drop 40) 40 uPcN_c1 (uClenN_chain (((Pc.reverse).drop 40).drop 40) 40 uPcN_c2 (uClenN_chain ((((Pc.reverse).drop 40).drop 40).drop 40) 40 uPcN_c3 (uPcN_end))))
theorem uSum_Pc : uSum Pc = shl 2 uPcN4.1 := uSum_of_N Pc uClenN_Pc
theorem uVcN_end : uClenN (((((Vc.reverse).drop 40).drop 40).drop 40).drop 40) uVcN4 = uVcN4 := by decide +kernel
end CatalanMeasure.GenD.D58.Cert590
