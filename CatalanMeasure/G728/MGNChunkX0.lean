module
public import CatalanMeasure.G728.MGNDefsX
@[expose] public section
namespace CatalanMeasure.G728
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem tNX_c0 : tfoldN ((Bsp_X).take 30) (([2], [0, 1]), []) = tNX1 := by decide +kernel
theorem tNX_c1 : tfoldN (((Bsp_X).drop 30).take 30) tNX1 = tNX2 := by decide +kernel
theorem tNX_c2 : tfoldN ((((Bsp_X).drop 30).drop 30).take 30) tNX2 = tNX3 := by decide +kernel
theorem tNX_c3 : tfoldN (((((Bsp_X).drop 30).drop 30).drop 30).take 30) tNX3 = tNX4 := by decide +kernel
theorem tNX_c4 : tfoldN ((((((Bsp_X).drop 30).drop 30).drop 30).drop 30).take 30) tNX4 = tNX5 := by decide +kernel
end CatalanMeasure.G728
