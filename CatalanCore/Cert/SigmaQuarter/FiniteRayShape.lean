module
public import CatalanCore.Cert.SigmaQuarter.FiniteRayData

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem rays_shape_check : (boxes rays).all (fun b => decide (rayShape b)) = true := by
  rw [rays_chunks]
  simp only [boxes_append, List.all_append, rayGeo0_shape, rayGeo1_shape, rayGeo2_shape, rayGeo3_shape, rayGeo4_shape, rayGeo5_shape, rayGeo6_shape, rayGeo7_shape, rayGeo8_shape, rayGeo9_shape, Bool.and_self]
end CatalanCore.Cert.SigmaQuarter
