module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_0 : logUpperOK (normChunksV.getD 0 []) (normBoundsV.getD 0 0)=true := by decide +kernel
theorem logChunkV_1 : logUpperOK (normChunksV.getD 1 []) (normBoundsV.getD 1 0)=true := by decide +kernel
theorem logChunkV_2 : logUpperOK (normChunksV.getD 2 []) (normBoundsV.getD 2 0)=true := by decide +kernel
theorem logChunkV_3 : logUpperOK (normChunksV.getD 3 []) (normBoundsV.getD 3 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
