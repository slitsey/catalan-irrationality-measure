module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkP_32 : logUpperOK (normChunksP.getD 32 []) (normBoundsP.getD 32 0)=true := by decide +kernel
theorem logChunkP_33 : logUpperOK (normChunksP.getD 33 []) (normBoundsP.getD 33 0)=true := by decide +kernel
theorem logChunkP_34 : logUpperOK (normChunksP.getD 34 []) (normBoundsP.getD 34 0)=true := by decide +kernel
theorem logChunkP_35 : logUpperOK (normChunksP.getD 35 []) (normBoundsP.getD 35 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
