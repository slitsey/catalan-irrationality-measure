module
public import CatalanCore.Cert.SigmaQuarter.FiniteSegData

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem scost_check : (-269717 / 10000000 : ℚ) ≤ ((boxes segs).map segCost).sum := by
  rw [segs_chunks]
  simp only [boxes_append, List.map_append, List.sum_append]
  rw [segGeo0_cost, segGeo1_cost, segGeo2_cost, segGeo3_cost, segGeo4_cost, segGeo5_cost, segGeo6_cost, segGeo7_cost, segGeo8_cost]
  norm_num
end CatalanCore.Cert.SigmaQuarter
