module
public import CatalanCore.Cert.QuarterContour.Glue
@[expose] public section
namespace CatalanCore.Cert.QuarterContour
open CatalanCore.Cert.SigmaQuarter

/-- The original rounded cell geometry contains every corresponding ray-tube point. -/
theorem rayShape_contains (sl r0 W : ℚ) (hsl : 0 < sl) (b : QBox)
    (hs : rayShape sl r0 W b) (u delta : ℝ)
    (hu1 : ((rayInterval sl b).1 : ℝ) ≤ u)
    (hu2 : u ≤ ((rayInterval sl b).2 : ℝ)) (hd : |delta| ≤ (W : ℝ)) :
    (b.1.1 : ℝ)/2^40 ≤ -(r0 : ℝ)+delta-u ∧
    -(r0 : ℝ)+delta-u ≤ (b.1.2.1 : ℝ)/2^40 ∧
    (b.1.2.2.1 : ℝ)/2^40 ≤ (sl : ℝ)*u ∧
    (sl : ℝ)*u ≤ (b.1.2.2.2 : ℝ)/2^40 := by
  have hslR : (0 : ℝ) < sl := Rat.cast_pos.mpr hsl
  have hlo := (Rat.cast_le (K := ℝ)).mpr hs.2.1
  have hhi := (Rat.cast_le (K := ℝ)).mpr hs.2.2
  push_cast at hlo hhi
  have hdelta := abs_le.mp hd
  have escale (q : ℤ) : (sl : ℝ)*(((q : ℚ)/(sl*2^40) : ℚ) : ℝ) = (q : ℝ)/2^40 := by
    push_cast
    field_simp [ne_of_gt hslR]
    <;> ring
  have hylo := mul_le_mul_of_nonneg_left hu1 hslR.le
  have hyhi := mul_le_mul_of_nonneg_left hu2 hslR.le
  change (sl : ℝ)*(((b.1.2.2.1 : ℚ)/(sl*2^40) : ℚ) : ℝ) ≤ _ at hylo
  change _ ≤ (sl : ℝ)*(((b.1.2.2.2 : ℚ)/(sl*2^40) : ℚ) : ℝ) at hyhi
  rw [escale] at hylo hyhi
  exact ⟨by linarith,by linarith,hylo,hyhi⟩

/-- Interval coverage turns checked per-cell ray-tube bounds into a uniform bound. -/
theorem ray_cells_cover_sound (f : ℝ → ℝ → ℝ) (sl r0 W lo hi mp : ℚ)
    (hsl : 0 < sl) (bs : List QBox)
    (hshape : ∀ b ∈ bs, rayShape sl r0 W b)
    (hcover : IntervalCovers (bs.map (rayInterval sl)) lo hi)
    (hsound : ∀ b ∈ bs, ∀ u delta : ℝ, |delta| ≤ (W : ℝ) →
      (b.1.1 : ℝ)/2^40 ≤ -(r0 : ℝ)+delta-u →
      -(r0 : ℝ)+delta-u ≤ (b.1.2.1 : ℝ)/2^40 →
      (b.1.2.2.1 : ℝ)/2^40 ≤ (sl : ℝ)*u →
      (sl : ℝ)*u ≤ (b.1.2.2.2 : ℝ)/2^40 →
      (mp : ℝ) ≤ f (-(r0 : ℝ)+delta-u) ((sl : ℝ)*u))
    (u delta : ℝ) (hu1 : (lo : ℝ) ≤ u) (hu2 : u ≤ (hi : ℝ))
    (hd : |delta| ≤ (W : ℝ)) :
    (mp : ℝ) ≤ f (-(r0 : ℝ)+delta-u) ((sl : ℝ)*u) := by
  obtain ⟨p,hp,ha,hb⟩ := hcover u hu1 hu2
  obtain ⟨b,hbmem,rfl⟩ := List.mem_map.mp hp
  rcases rayShape_contains sl r0 W hsl b (hshape b hbmem) u delta ha hb hd with ⟨h1,h2,h3,h4⟩
  exact hsound b hbmem u delta hd h1 h2 h3 h4

end CatalanCore.Cert.QuarterContour
#print axioms CatalanCore.Cert.QuarterContour.ray_cells_cover_sound
