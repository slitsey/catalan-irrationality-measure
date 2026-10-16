module
public import CatalanMeasure.StrongTrial.NormLogData
public import CatalanMeasure.Cert.SplitNorm
@[expose] public section
namespace CatalanMeasure.StrongTrial
open CatalanMeasure.Cert OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem logChunkP_44 : logUpperOK (normChunksP.getD 44 []) (normBoundsP.getD 44 0)=true := by decide +kernel
end CatalanMeasure.StrongTrial
