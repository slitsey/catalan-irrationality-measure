module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkP_8 : logUpperOK (normChunksP.getD 8 []) (normBoundsP.getD 8 0)=true := by decide +kernel
theorem logChunkP_9 : logUpperOK (normChunksP.getD 9 []) (normBoundsP.getD 9 0)=true := by decide +kernel
theorem logChunkP_10 : logUpperOK (normChunksP.getD 10 []) (normBoundsP.getD 10 0)=true := by decide +kernel
theorem logChunkP_11 : logUpperOK (normChunksP.getD 11 []) (normBoundsP.getD 11 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
