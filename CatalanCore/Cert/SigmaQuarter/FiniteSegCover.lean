module
public import CatalanCore.Cert.SigmaQuarter.FiniteSegData

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem seg_cover_check : IntervalCovers (intervals segs) (-1 / 10 : ℚ) (0 / 1 : ℚ) := by
  rw [segs_chunks]
  simp only [intervals_append]
  exact intervalCovers_restrict (intervalCovers_append segGeo0_cover (intervalCovers_append segGeo1_cover (intervalCovers_append segGeo2_cover (intervalCovers_append segGeo3_cover (intervalCovers_append segGeo4_cover (intervalCovers_append segGeo5_cover (intervalCovers_append segGeo6_cover (intervalCovers_append segGeo7_cover (intervalCovers_append segGeo8_cover (intervalCovers_append segGeo9_cover (segGeo10_cover) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num) (by norm_num)
end CatalanCore.Cert.SigmaQuarter
