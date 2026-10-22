module
public import CatalanCore.Cert.SigmaQuarter.FiniteLineData

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem lines_shape_check : (boxes lines).all (fun b => decide (lineShape b)) = true := by
  rw [lines_chunks]
  simp only [boxes_append, List.all_append, lineGeo0_shape, lineGeo1_shape, lineGeo2_shape, lineGeo3_shape, lineGeo4_shape, lineGeo5_shape, lineGeo6_shape, lineGeo7_shape, lineGeo8_shape, Bool.and_self]
end CatalanCore.Cert.SigmaQuarter
