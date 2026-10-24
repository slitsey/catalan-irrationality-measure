module
public import CatalanArchive.CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkP_4 : logUpperOK (normChunksP.getD 4 []) (normBoundsP.getD 4 0)=true := by decide +kernel
theorem logChunkP_5 : logUpperOK (normChunksP.getD 5 []) (normBoundsP.getD 5 0)=true := by decide +kernel
theorem logChunkP_6 : logUpperOK (normChunksP.getD 6 []) (normBoundsP.getD 6 0)=true := by decide +kernel
theorem logChunkP_7 : logUpperOK (normChunksP.getD 7 []) (normBoundsP.getD 7 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
