module
public import CatalanCore.Cert.SigmaQuarterContour.Data
public import CatalanCore.Cert.QuarterContour.Energy
public import CatalanCore.Cert.QuarterContour.FastArithmetic
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarterContour.EagerPilot
open CatalanCore.Cert.QuarterContour
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option cbv.warning false
set_option cbv.maxSteps 10000000
set_option Elab.async false
set_option profiler true in
 theorem row0 : QuarterContour.iRow (pointAt pts 0) pts = (69597188796915915233807754584 : ℤ) := by cbv
end CatalanCore.Cert.SigmaQuarterContour.EagerPilot
#print axioms CatalanCore.Cert.SigmaQuarterContour.EagerPilot.row0