module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_40 : logUpperOK (normChunksV.getD 40 []) (normBoundsV.getD 40 0)=true := by decide +kernel
theorem logChunkV_41 : logUpperOK (normChunksV.getD 41 []) (normBoundsV.getD 41 0)=true := by decide +kernel
theorem logChunkV_42 : logUpperOK (normChunksV.getD 42 []) (normBoundsV.getD 42 0)=true := by decide +kernel
theorem logChunkV_43 : logUpperOK (normChunksV.getD 43 []) (normBoundsV.getD 43 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
