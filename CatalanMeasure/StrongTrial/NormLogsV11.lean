module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_44 : logUpperOK (normChunksV.getD 44 []) (normBoundsV.getD 44 0)=true := by decide +kernel
theorem logChunkV_45 : logUpperOK (normChunksV.getD 45 []) (normBoundsV.getD 45 0)=true := by decide +kernel
theorem logChunkV_46 : logUpperOK (normChunksV.getD 46 []) (normBoundsV.getD 46 0)=true := by decide +kernel
theorem logChunkV_47 : logUpperOK (normChunksV.getD 47 []) (normBoundsV.getD 47 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
