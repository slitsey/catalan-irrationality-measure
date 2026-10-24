module
public import CatalanArchive.CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_16 : logUpperOK (normChunksV.getD 16 []) (normBoundsV.getD 16 0)=true := by decide +kernel
theorem logChunkV_17 : logUpperOK (normChunksV.getD 17 []) (normBoundsV.getD 17 0)=true := by decide +kernel
theorem logChunkV_18 : logUpperOK (normChunksV.getD 18 []) (normBoundsV.getD 18 0)=true := by decide +kernel
theorem logChunkV_19 : logUpperOK (normChunksV.getD 19 []) (normBoundsV.getD 19 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
