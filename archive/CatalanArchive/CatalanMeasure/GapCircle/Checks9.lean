module
public import CatalanArchive.CatalanMeasure.GapCircle.Data
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem check36 : piece36.OK=true := by decide +kernel
theorem check37 : piece37.OK=true := by decide +kernel
theorem check38 : piece38.OK=true := by decide +kernel
theorem check39 : piece39.OK=true := by decide +kernel
end CatalanMeasure.GapCircle
