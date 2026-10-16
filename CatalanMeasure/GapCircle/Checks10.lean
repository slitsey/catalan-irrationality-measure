module
public import CatalanMeasure.GapCircle.Data
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem check40 : piece40.OK=true := by decide +kernel
theorem check41 : piece41.OK=true := by decide +kernel
theorem check42 : piece42.OK=true := by decide +kernel
theorem check43 : piece43.OK=true := by decide +kernel
end CatalanMeasure.GapCircle
