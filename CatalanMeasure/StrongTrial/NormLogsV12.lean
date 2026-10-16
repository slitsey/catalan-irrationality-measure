module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_48 : logUpperOK (normChunksV.getD 48 []) (normBoundsV.getD 48 0)=true := by decide +kernel
theorem logChunkV_49 : logUpperOK (normChunksV.getD 49 []) (normBoundsV.getD 49 0)=true := by decide +kernel
theorem logChunkV_50 : logUpperOK (normChunksV.getD 50 []) (normBoundsV.getD 50 0)=true := by decide +kernel
theorem logChunkV_51 : logUpperOK (normChunksV.getD 51 []) (normBoundsV.getD 51 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
