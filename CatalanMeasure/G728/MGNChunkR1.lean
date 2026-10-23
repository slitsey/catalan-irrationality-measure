module
public import CatalanMeasure.G728.MGNDefsR
@[expose] public section
namespace CatalanMeasure.G728
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem tNR_c5 : tfoldN (((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).take 30) tNR5 = tNR6 := by decide +kernel
theorem tNR_c6 : tfoldN ((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).take 30) tNR6 = tNR7 := by decide +kernel
theorem tNR_c7 : tfoldN (((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).take 30) tNR7 = tNR8 := by decide +kernel
theorem tNR_c8 : tfoldN ((((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).take 30) tNR8 = tNR9 := by decide +kernel
theorem tNR_c9 : tfoldN (((((((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).drop 30).take 30) tNR9 = tNR10 := by decide +kernel
end CatalanMeasure.G728
