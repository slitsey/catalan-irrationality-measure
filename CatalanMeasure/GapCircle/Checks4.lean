module
public import CatalanMeasure.GapCircle.Data
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem check16 : piece16.OK=true := by decide +kernel
theorem check17 : piece17.OK=true := by decide +kernel
theorem check18 : piece18.OK=true := by decide +kernel
theorem check19 : piece19.OK=true := by decide +kernel
end CatalanMeasure.GapCircle
