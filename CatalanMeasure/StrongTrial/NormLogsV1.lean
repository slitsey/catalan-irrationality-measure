module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_4 : logUpperOK (normChunksV.getD 4 []) (normBoundsV.getD 4 0)=true := by decide +kernel
theorem logChunkV_5 : logUpperOK (normChunksV.getD 5 []) (normBoundsV.getD 5 0)=true := by decide +kernel
theorem logChunkV_6 : logUpperOK (normChunksV.getD 6 []) (normBoundsV.getD 6 0)=true := by decide +kernel
theorem logChunkV_7 : logUpperOK (normChunksV.getD 7 []) (normBoundsV.getD 7 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
