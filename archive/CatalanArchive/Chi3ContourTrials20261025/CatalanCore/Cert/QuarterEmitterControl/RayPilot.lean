module
public import CatalanCore.Cert.QuarterEmitterControl.Data
public import CatalanCore.Cert.QuarterContour.Macros
@[expose] public section
namespace CatalanCore.Cert.QuarterEmitterControl
open CatalanCore.Cert.SigmaQuarter CatalanCore.Cert.QuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
def pilot : Macro := ⟨0, 0, 0, 1558, (0,0,0,0,0,0), [((-164927793767, -164926743142, 164926744166, 164929889895), (-109951862512, -109951162094, 109951162777, 109953259930))]⟩
theorem pilot_far : farOK pts pilot := by decide +kernel
theorem pilot_ray : QuarterContour.rayOK (1/100000) pts (7226/3125) pilot = true := by decide +kernel
end CatalanCore.Cert.QuarterEmitterControl
#print axioms CatalanCore.Cert.QuarterEmitterControl.pilot_far
#print axioms CatalanCore.Cert.QuarterEmitterControl.pilot_ray
