module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkP_16 : logUpperOK (normChunksP.getD 16 []) (normBoundsP.getD 16 0)=true := by decide +kernel
theorem logChunkP_17 : logUpperOK (normChunksP.getD 17 []) (normBoundsP.getD 17 0)=true := by decide +kernel
theorem logChunkP_18 : logUpperOK (normChunksP.getD 18 []) (normBoundsP.getD 18 0)=true := by decide +kernel
theorem logChunkP_19 : logUpperOK (normChunksP.getD 19 []) (normBoundsP.getD 19 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
