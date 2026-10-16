module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_24 : logUpperOK (normChunksV.getD 24 []) (normBoundsV.getD 24 0)=true := by decide +kernel
theorem logChunkV_25 : logUpperOK (normChunksV.getD 25 []) (normBoundsV.getD 25 0)=true := by decide +kernel
theorem logChunkV_26 : logUpperOK (normChunksV.getD 26 []) (normBoundsV.getD 26 0)=true := by decide +kernel
theorem logChunkV_27 : logUpperOK (normChunksV.getD 27 []) (normBoundsV.getD 27 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
