module
public import CatalanArchive.CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkP_28 : logUpperOK (normChunksP.getD 28 []) (normBoundsP.getD 28 0)=true := by decide +kernel
theorem logChunkP_29 : logUpperOK (normChunksP.getD 29 []) (normBoundsP.getD 29 0)=true := by decide +kernel
theorem logChunkP_30 : logUpperOK (normChunksP.getD 30 []) (normBoundsP.getD 30 0)=true := by decide +kernel
theorem logChunkP_31 : logUpperOK (normChunksP.getD 31 []) (normBoundsP.getD 31 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
