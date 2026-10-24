module
public import CatalanArchive.CatalanMeasure.GapCircle.Data
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem check28 : piece28.OK=true := by decide +kernel
theorem check29 : piece29.OK=true := by decide +kernel
theorem check30 : piece30.OK=true := by decide +kernel
theorem check31 : piece31.OK=true := by decide +kernel
end CatalanMeasure.GapCircle
