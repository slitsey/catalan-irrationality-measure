module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkP_12 : logUpperOK (normChunksP.getD 12 []) (normBoundsP.getD 12 0)=true := by decide +kernel
theorem logChunkP_13 : logUpperOK (normChunksP.getD 13 []) (normBoundsP.getD 13 0)=true := by decide +kernel
theorem logChunkP_14 : logUpperOK (normChunksP.getD 14 []) (normBoundsP.getD 14 0)=true := by decide +kernel
theorem logChunkP_15 : logUpperOK (normChunksP.getD 15 []) (normBoundsP.getD 15 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
