module
public import CatalanMeasure.G728.ZNDefs
@[expose] public section
namespace CatalanMeasure.G728
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem uVcN_c0 : uClenN ((Vc.reverse).take 40) ([], []) = uVcN1 := by decide +kernel
theorem uVcN_c1 : uClenN (((Vc.reverse).drop 40).take 40) uVcN1 = uVcN2 := by decide +kernel
theorem uVcN_c2 : uClenN ((((Vc.reverse).drop 40).drop 40).take 40) uVcN2 = uVcN3 := by decide +kernel
theorem uVcN_c3 : uClenN (((((Vc.reverse).drop 40).drop 40).drop 40).take 40) uVcN3 = uVcN4 := by decide +kernel
end CatalanMeasure.G728
