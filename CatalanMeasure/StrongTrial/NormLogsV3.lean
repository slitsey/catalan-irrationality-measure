module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_12 : logUpperOK (normChunksV.getD 12 []) (normBoundsV.getD 12 0)=true := by decide +kernel
theorem logChunkV_13 : logUpperOK (normChunksV.getD 13 []) (normBoundsV.getD 13 0)=true := by decide +kernel
theorem logChunkV_14 : logUpperOK (normChunksV.getD 14 []) (normBoundsV.getD 14 0)=true := by decide +kernel
theorem logChunkV_15 : logUpperOK (normChunksV.getD 15 []) (normBoundsV.getD 15 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
