module
public import CatalanMeasure.GapCircle.Data
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem check48 : piece48.OK=true := by decide +kernel
theorem check49 : piece49.OK=true := by decide +kernel
theorem check50 : piece50.OK=true := by decide +kernel
theorem check51 : piece51.OK=true := by decide +kernel
end CatalanMeasure.GapCircle
