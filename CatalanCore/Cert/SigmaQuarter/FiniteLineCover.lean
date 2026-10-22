module
public import CatalanCore.Cert.SigmaQuarter.FiniteLineData

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem line_cover_check : IntervalCovers (intervals lines) (0 / 1 : ℚ) (1 / 1 : ℚ) := by
  rw [lines_chunks]
  simp only [intervals_append]
  exact intervalCovers_restrict (intervalCovers_append lineGeo0_cover (intervalCovers_append lineGeo1_cover (intervalCovers_append lineGeo2_cover (intervalCovers_append lineGeo3_cover (intervalCovers_append lineGeo4_cover (intervalCovers_append lineGeo5_cover (intervalCovers_append lineGeo6_cover (intervalCovers_append lineGeo7_cover (lineGeo8_cover) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num) (by norm_num)
end CatalanCore.Cert.SigmaQuarter
