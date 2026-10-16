module
public import CatalanMeasure.GapCircle.Data
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem check52 : piece52.OK=true := by decide +kernel
theorem check53 : piece53.OK=true := by decide +kernel
theorem check54 : piece54.OK=true := by decide +kernel
end CatalanMeasure.GapCircle
