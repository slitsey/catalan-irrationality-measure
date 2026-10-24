module
public import CatalanArchive.CatalanMeasure.GapCircle.Data
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem check24 : piece24.OK=true := by decide +kernel
theorem check25 : piece25.OK=true := by decide +kernel
theorem check26 : piece26.OK=true := by decide +kernel
theorem check27 : piece27.OK=true := by decide +kernel
end CatalanMeasure.GapCircle
