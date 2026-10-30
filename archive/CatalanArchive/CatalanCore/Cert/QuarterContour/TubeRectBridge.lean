module
public import CatalanCore.Decay.Rect.CertG
@[expose] public section
namespace CatalanCore.Cert.QuarterContour

/-- Narrow rectangles inherit a ray-tube bound.  This allows the existing
certificate interface to consume a direct tube proof, with a smaller window. -/
theorem rectangle_of_ray_tube (g : ℂ → ℝ) (sl r0 W R umax mp : ℝ)
    (hsl : 0 < sl)
    (htube : ∀ u delta : ℝ, 0 ≤ u → u ≤ umax → |delta| ≤ R →
      mp ≤ g ⟨-r0+delta-u,sl*u⟩)
    (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ umax) (hwidth : b-a+W ≤ R)
    (x y : ℝ) (hx1 : -r0-b-W ≤ x) (hx2 : x ≤ -r0-a+W)
    (hy1 : sl*a ≤ y) (hy2 : y ≤ sl*b) : mp ≤ g ⟨x,y⟩ := by
  let u : ℝ := y/sl
  have hau : a ≤ u := (le_div_iff₀ hsl).mpr (by simpa only [mul_comm] using hy1)
  have hub : u ≤ b := (div_le_iff₀ hsl).mpr (by simpa only [mul_comm] using hy2)
  have hd : |x+r0+u| ≤ R := by
    apply abs_le.mpr
    constructor <;> linarith
  have h := htube u (x+r0+u) (ha.trans hau) (hub.trans hb) hd
  have ex : -r0+(x+r0+u)-u = x := by ring
  have ey : sl*u = y := by dsimp [u]; field_simp
  simpa only [ex,ey] using h

end CatalanCore.Cert.QuarterContour
#print axioms CatalanCore.Cert.QuarterContour.rectangle_of_ray_tube
