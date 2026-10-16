module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkP_24 : logUpperOK (normChunksP.getD 24 []) (normBoundsP.getD 24 0)=true := by decide +kernel
theorem logChunkP_25 : logUpperOK (normChunksP.getD 25 []) (normBoundsP.getD 25 0)=true := by decide +kernel
theorem logChunkP_26 : logUpperOK (normChunksP.getD 26 []) (normBoundsP.getD 26 0)=true := by decide +kernel
theorem logChunkP_27 : logUpperOK (normChunksP.getD 27 []) (normBoundsP.getD 27 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
