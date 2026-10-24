module
public import CatalanArchive.CatalanMeasure.GapCircle.Data
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem check44 : piece44.OK=true := by decide +kernel
theorem check45 : piece45.OK=true := by decide +kernel
theorem check46 : piece46.OK=true := by decide +kernel
theorem check47 : piece47.OK=true := by decide +kernel
end CatalanMeasure.GapCircle
