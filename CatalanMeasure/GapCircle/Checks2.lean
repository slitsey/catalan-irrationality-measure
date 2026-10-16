module
public import CatalanMeasure.GapCircle.Data
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem check8 : piece8.OK=true := by decide +kernel
theorem check9 : piece9.OK=true := by decide +kernel
theorem check10 : piece10.OK=true := by decide +kernel
theorem check11 : piece11.OK=true := by decide +kernel
end CatalanMeasure.GapCircle
