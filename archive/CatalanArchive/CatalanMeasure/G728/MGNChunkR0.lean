module
public import CatalanArchive.CatalanMeasure.G728.MGNDefsR
@[expose] public section
namespace CatalanMeasure.G728
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem tNR_c0 : tfoldN ((Bsp_R).take 30) (([2], [0, 1]), []) = tNR1 := by decide +kernel
theorem tNR_c1 : tfoldN (((Bsp_R).drop 30).take 30) tNR1 = tNR2 := by decide +kernel
theorem tNR_c2 : tfoldN ((((Bsp_R).drop 30).drop 30).take 30) tNR2 = tNR3 := by decide +kernel
theorem tNR_c3 : tfoldN (((((Bsp_R).drop 30).drop 30).drop 30).take 30) tNR3 = tNR4 := by decide +kernel
theorem tNR_c4 : tfoldN ((((((Bsp_R).drop 30).drop 30).drop 30).drop 30).take 30) tNR4 = tNR5 := by decide +kernel
end CatalanMeasure.G728
