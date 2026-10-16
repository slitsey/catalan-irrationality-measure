module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_8 : logUpperOK (normChunksV.getD 8 []) (normBoundsV.getD 8 0)=true := by decide +kernel
theorem logChunkV_9 : logUpperOK (normChunksV.getD 9 []) (normBoundsV.getD 9 0)=true := by decide +kernel
theorem logChunkV_10 : logUpperOK (normChunksV.getD 10 []) (normBoundsV.getD 10 0)=true := by decide +kernel
theorem logChunkV_11 : logUpperOK (normChunksV.getD 11 []) (normBoundsV.getD 11 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
