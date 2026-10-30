module
public import CatalanCore.Cert.SigmaQuarterContour.Data
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem checkChunk_15 : (checkChunk 15).all pointOK = true := by decide +kernel
end CatalanCore.Cert.SigmaQuarterContour
