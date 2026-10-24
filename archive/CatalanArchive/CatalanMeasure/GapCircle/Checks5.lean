module
public import CatalanArchive.CatalanMeasure.GapCircle.Data
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem check20 : piece20.OK=true := by decide +kernel
theorem check21 : piece21.OK=true := by decide +kernel
theorem check22 : piece22.OK=true := by decide +kernel
theorem check23 : piece23.OK=true := by decide +kernel
end CatalanMeasure.GapCircle
