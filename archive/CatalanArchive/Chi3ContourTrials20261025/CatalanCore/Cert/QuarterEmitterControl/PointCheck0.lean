module
public import CatalanCore.Cert.QuarterEmitterControl.Data
@[expose] public section
namespace CatalanCore.Cert.QuarterEmitterControl
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
theorem checkChunk_0 : (checkChunk 0).all pointOK = true := by decide +kernel
end CatalanCore.Cert.QuarterEmitterControl
