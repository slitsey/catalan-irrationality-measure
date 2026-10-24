module
public import CatalanArchive.CatalanMeasure.G728.MGNDefsY
@[expose] public section
namespace CatalanMeasure.G728
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem tNY_c0 : tfoldN ((Bsp_Y).take 30) (([2], [0, 1]), []) = tNY1 := by decide +kernel
theorem tNY_c1 : tfoldN (((Bsp_Y).drop 30).take 30) tNY1 = tNY2 := by decide +kernel
theorem tNY_c2 : tfoldN ((((Bsp_Y).drop 30).drop 30).take 30) tNY2 = tNY3 := by decide +kernel
theorem tNY_c3 : tfoldN (((((Bsp_Y).drop 30).drop 30).drop 30).take 30) tNY3 = tNY4 := by decide +kernel
theorem tNY_c4 : tfoldN ((((((Bsp_Y).drop 30).drop 30).drop 30).drop 30).take 30) tNY4 = tNY5 := by decide +kernel
end CatalanMeasure.G728
