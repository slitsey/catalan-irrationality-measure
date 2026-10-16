module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkP_20 : logUpperOK (normChunksP.getD 20 []) (normBoundsP.getD 20 0)=true := by decide +kernel
theorem logChunkP_21 : logUpperOK (normChunksP.getD 21 []) (normBoundsP.getD 21 0)=true := by decide +kernel
theorem logChunkP_22 : logUpperOK (normChunksP.getD 22 []) (normBoundsP.getD 22 0)=true := by decide +kernel
theorem logChunkP_23 : logUpperOK (normChunksP.getD 23 []) (normBoundsP.getD 23 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
