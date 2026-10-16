module
public import CatalanMeasure.GapCircle.Data
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem check32 : piece32.OK=true := by decide +kernel
theorem check33 : piece33.OK=true := by decide +kernel
theorem check34 : piece34.OK=true := by decide +kernel
theorem check35 : piece35.OK=true := by decide +kernel
end CatalanMeasure.GapCircle
