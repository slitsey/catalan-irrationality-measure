module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_56 : logUpperOK (normChunksV.getD 56 []) (normBoundsV.getD 56 0)=true := by decide +kernel
theorem logChunkV_57 : logUpperOK (normChunksV.getD 57 []) (normBoundsV.getD 57 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
