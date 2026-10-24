module
public import CatalanArchive.CatalanMeasure.GapCircle.Data
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem check4 : piece4.OK=true := by decide +kernel
theorem check5 : piece5.OK=true := by decide +kernel
theorem check6 : piece6.OK=true := by decide +kernel
theorem check7 : piece7.OK=true := by decide +kernel
end CatalanMeasure.GapCircle
