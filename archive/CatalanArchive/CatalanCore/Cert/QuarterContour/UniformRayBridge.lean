module
public import CatalanCore.Cert.QuarterContour.UniformRayGrid
public import CatalanCore.Cert.QuarterContour.TubeRectBridge
@[expose] public section
namespace CatalanCore.Cert.QuarterContour

/-- Symbolic fine rectangles let the legacy certificate interface consume a direct
ray-tube theorem.  The grid is never enumerated or checked numerically. -/
theorem uniform_rectangles_of_ray_tube (g : ℂ → ℝ)
    (sl r0 W R U mp : ℚ) (N : ℕ) (hsl : 0 < sl) (hN : 0 < N) (hU : 0 ≤ U)
    (hwidth : U/(N : ℚ)+W ≤ R)
    (htube : ∀ u delta : ℝ, 0 ≤ u → u ≤ (U : ℝ) → |delta| ≤ (R : ℝ) →
      (mp : ℝ) ≤ g ⟨-(r0 : ℝ)+delta-u,(sl : ℝ)*u⟩)
    (p : ℚ × ℚ) (hp : p ∈ UniformRayGrid.intervals N U)
    (x y : ℝ) (hx1 : -(r0 : ℝ)-(p.2 : ℝ)-W ≤ x)
    (hx2 : x ≤ -(r0 : ℝ)-(p.1 : ℝ)+W)
    (hy1 : (sl : ℝ)*(p.1 : ℝ) ≤ y) (hy2 : y ≤ (sl : ℝ)*(p.2 : ℝ)) :
    (mp : ℝ) ≤ g ⟨x,y⟩ := by
  have hb := UniformRayGrid.bounds N U hN hU p hp
  have hw : p.2-p.1+W ≤ R := by
    rw [UniformRayGrid.width N U p hp]
    exact hwidth
  have hwR := (Rat.cast_le (K := ℝ)).mpr hw
  push_cast at hwR
  exact rectangle_of_ray_tube g sl r0 W R U mp (Rat.cast_pos.mpr hsl) htube
    p.1 p.2 (Rat.cast_nonneg.mpr hb.1) (Rat.cast_le.mpr hb.2.2) hwR x y hx1 hx2 hy1 hy2

/-- The chosen smaller window leaves enough room for each symbolic rectangle. -/
theorem quarter_grid_width : (3/2 : ℚ)/(2^32 : ℕ)+1/2^32 ≤ 1/2^30 := by norm_num

end CatalanCore.Cert.QuarterContour
#print axioms CatalanCore.Cert.QuarterContour.uniform_rectangles_of_ray_tube
#print axioms CatalanCore.Cert.QuarterContour.quarter_grid_width
