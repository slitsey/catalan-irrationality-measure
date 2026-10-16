module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_28 : logUpperOK (normChunksV.getD 28 []) (normBoundsV.getD 28 0)=true := by decide +kernel
theorem logChunkV_29 : logUpperOK (normChunksV.getD 29 []) (normBoundsV.getD 29 0)=true := by decide +kernel
theorem logChunkV_30 : logUpperOK (normChunksV.getD 30 []) (normBoundsV.getD 30 0)=true := by decide +kernel
theorem logChunkV_31 : logUpperOK (normChunksV.getD 31 []) (normBoundsV.getD 31 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
