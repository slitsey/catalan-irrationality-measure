module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkP_0 : logUpperOK (normChunksP.getD 0 []) (normBoundsP.getD 0 0)=true := by decide +kernel
theorem logChunkP_1 : logUpperOK (normChunksP.getD 1 []) (normBoundsP.getD 1 0)=true := by decide +kernel
theorem logChunkP_2 : logUpperOK (normChunksP.getD 2 []) (normBoundsP.getD 2 0)=true := by decide +kernel
theorem logChunkP_3 : logUpperOK (normChunksP.getD 3 []) (normBoundsP.getD 3 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
