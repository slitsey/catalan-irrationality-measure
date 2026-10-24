module
public import CatalanArchive.CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkP_36 : logUpperOK (normChunksP.getD 36 []) (normBoundsP.getD 36 0)=true := by decide +kernel
theorem logChunkP_37 : logUpperOK (normChunksP.getD 37 []) (normBoundsP.getD 37 0)=true := by decide +kernel
theorem logChunkP_38 : logUpperOK (normChunksP.getD 38 []) (normBoundsP.getD 38 0)=true := by decide +kernel
theorem logChunkP_39 : logUpperOK (normChunksP.getD 39 []) (normBoundsP.getD 39 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
