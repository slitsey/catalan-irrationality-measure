module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_20 : logUpperOK (normChunksV.getD 20 []) (normBoundsV.getD 20 0)=true := by decide +kernel
theorem logChunkV_21 : logUpperOK (normChunksV.getD 21 []) (normBoundsV.getD 21 0)=true := by decide +kernel
theorem logChunkV_22 : logUpperOK (normChunksV.getD 22 []) (normBoundsV.getD 22 0)=true := by decide +kernel
theorem logChunkV_23 : logUpperOK (normChunksV.getD 23 []) (normBoundsV.getD 23 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
