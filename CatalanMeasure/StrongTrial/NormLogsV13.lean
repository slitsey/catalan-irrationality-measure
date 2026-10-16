module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkV_52 : logUpperOK (normChunksV.getD 52 []) (normBoundsV.getD 52 0)=true := by decide +kernel
theorem logChunkV_53 : logUpperOK (normChunksV.getD 53 []) (normBoundsV.getD 53 0)=true := by decide +kernel
theorem logChunkV_54 : logUpperOK (normChunksV.getD 54 []) (normBoundsV.getD 54 0)=true := by decide +kernel
theorem logChunkV_55 : logUpperOK (normChunksV.getD 55 []) (normBoundsV.getD 55 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
