module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_32 : logUpperOK (normChunksV.getD 32 []) (normBoundsV.getD 32 0)=true := by decide +kernel
theorem logChunkV_33 : logUpperOK (normChunksV.getD 33 []) (normBoundsV.getD 33 0)=true := by decide +kernel
theorem logChunkV_34 : logUpperOK (normChunksV.getD 34 []) (normBoundsV.getD 34 0)=true := by decide +kernel
theorem logChunkV_35 : logUpperOK (normChunksV.getD 35 []) (normBoundsV.getD 35 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
