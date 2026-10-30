module
public import CatalanCore.Cert.SigmaQuarter.PointCheckDef
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checkChunk_15 : (checkChunk 15).all pointCheck = true := by decide +kernel
end CatalanCore.Cert.SigmaQuarter
