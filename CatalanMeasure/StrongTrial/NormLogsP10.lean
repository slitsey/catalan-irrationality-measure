module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkP_40 : logUpperOK (normChunksP.getD 40 []) (normBoundsP.getD 40 0)=true := by decide +kernel
theorem logChunkP_41 : logUpperOK (normChunksP.getD 41 []) (normBoundsP.getD 41 0)=true := by decide +kernel
theorem logChunkP_42 : logUpperOK (normChunksP.getD 42 []) (normBoundsP.getD 42 0)=true := by decide +kernel
theorem logChunkP_43 : logUpperOK (normChunksP.getD 43 []) (normBoundsP.getD 43 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
