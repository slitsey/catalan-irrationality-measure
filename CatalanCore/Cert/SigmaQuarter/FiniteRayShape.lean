module
public import CatalanCore.Cert.SigmaQuarter.FiniteRayData

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem rays_shape_check : (boxes rays).all (fun b => decide (rayShape b)) = true := by
  rw [rays_chunks]
  simp only [boxes_append, List.all_append, rayGeo0_shape, rayGeo1_shape, rayGeo2_shape, rayGeo3_shape, rayGeo4_shape, rayGeo5_shape, rayGeo6_shape, rayGeo7_shape, rayGeo8_shape, rayGeo9_shape, rayGeo10_shape, rayGeo11_shape, rayGeo12_shape, rayGeo13_shape, rayGeo14_shape, rayGeo15_shape, rayGeo16_shape, rayGeo17_shape, rayGeo18_shape, rayGeo19_shape, rayGeo20_shape, rayGeo21_shape, rayGeo22_shape, rayGeo23_shape, rayGeo24_shape, rayGeo25_shape, rayGeo26_shape, rayGeo27_shape, rayGeo28_shape, rayGeo29_shape, rayGeo30_shape, rayGeo31_shape, rayGeo32_shape, rayGeo33_shape, rayGeo34_shape, rayGeo35_shape, rayGeo36_shape, rayGeo37_shape, rayGeo38_shape, rayGeo39_shape, rayGeo40_shape, rayGeo41_shape, rayGeo42_shape, rayGeo43_shape, rayGeo44_shape, rayGeo45_shape, rayGeo46_shape, rayGeo47_shape, rayGeo48_shape, rayGeo49_shape, rayGeo50_shape, rayGeo51_shape, rayGeo52_shape, rayGeo53_shape, rayGeo54_shape, rayGeo55_shape, rayGeo56_shape, rayGeo57_shape, rayGeo58_shape, rayGeo59_shape, rayGeo60_shape, rayGeo61_shape, rayGeo62_shape, Bool.and_self]
end CatalanCore.Cert.SigmaQuarter
