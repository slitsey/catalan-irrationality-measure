module
public import CatalanMeasure.GapCircle.Data
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem check0 : piece0.OK=true := by decide +kernel
theorem check1 : piece1.OK=true := by decide +kernel
theorem check2 : piece2.OK=true := by decide +kernel
theorem check3 : piece3.OK=true := by decide +kernel
end CatalanMeasure.GapCircle
