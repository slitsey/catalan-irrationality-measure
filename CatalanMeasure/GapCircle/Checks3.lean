module
public import CatalanMeasure.GapCircle.Data
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem check12 : piece12.OK=true := by decide +kernel
theorem check13 : piece13.OK=true := by decide +kernel
theorem check14 : piece14.OK=true := by decide +kernel
theorem check15 : piece15.OK=true := by decide +kernel
end CatalanMeasure.GapCircle
