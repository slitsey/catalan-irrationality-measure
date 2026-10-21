module
public import CatalanCore.Cert.SigmaQuarter.FiniteSegData

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem segs_shape_check : (boxes segs).all (fun b => decide (segShape b)) = true := by
  rw [segs_chunks]
  simp only [boxes_append, List.all_append, segGeo0_shape, segGeo1_shape, segGeo2_shape, segGeo3_shape, segGeo4_shape, segGeo5_shape, segGeo6_shape, segGeo7_shape, segGeo8_shape, Bool.and_self]
end CatalanCore.Cert.SigmaQuarter
