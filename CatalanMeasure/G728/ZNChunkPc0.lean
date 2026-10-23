module
public import CatalanMeasure.G728.ZNDefs
@[expose] public section
namespace CatalanMeasure.G728
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem uPcN_c0 : uClenN ((Pc.reverse).take 40) ([], []) = uPcN1 := by decide +kernel
theorem uPcN_c1 : uClenN (((Pc.reverse).drop 40).take 40) uPcN1 = uPcN2 := by decide +kernel
theorem uPcN_c2 : uClenN ((((Pc.reverse).drop 40).drop 40).take 40) uPcN2 = uPcN3 := by decide +kernel
theorem uPcN_c3 : uClenN (((((Pc.reverse).drop 40).drop 40).drop 40).take 40) uPcN3 = uPcN4 := by decide +kernel
end CatalanMeasure.G728
