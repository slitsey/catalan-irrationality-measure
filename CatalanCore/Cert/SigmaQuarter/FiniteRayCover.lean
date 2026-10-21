module
public import CatalanCore.Cert.SigmaQuarter.FiniteRayData

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem ray_cover_check : IntervalCovers (rayIntervals rays) (0 / 1 : ℚ) (3 / 2 : ℚ) := by
  rw [rays_chunks]
  simp only [rayIntervals_append, List.append_assoc]
  exact intervalCovers_restrict (intervalCovers_append rayGeo0_cover (intervalCovers_append rayGeo1_cover (intervalCovers_append rayGeo2_cover (intervalCovers_append rayGeo3_cover (intervalCovers_append rayGeo4_cover (intervalCovers_append rayGeo5_cover (intervalCovers_append rayGeo6_cover (intervalCovers_append rayGeo7_cover (intervalCovers_append rayGeo8_cover (rayGeo9_cover) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num)) (by norm_num) (by norm_num)
end CatalanCore.Cert.SigmaQuarter
