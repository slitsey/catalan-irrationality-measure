module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_36 : logUpperOK (normChunksV.getD 36 []) (normBoundsV.getD 36 0)=true := by decide +kernel
theorem logChunkV_37 : logUpperOK (normChunksV.getD 37 []) (normBoundsV.getD 37 0)=true := by decide +kernel
theorem logChunkV_38 : logUpperOK (normChunksV.getD 38 []) (normBoundsV.getD 38 0)=true := by decide +kernel
theorem logChunkV_39 : logUpperOK (normChunksV.getD 39 []) (normBoundsV.getD 39 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
