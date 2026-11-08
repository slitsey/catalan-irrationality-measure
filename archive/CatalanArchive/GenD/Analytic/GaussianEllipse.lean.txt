module
public import CatalanMeasure.GenD.Analytic.GaussianCertificate
public import CatalanMeasure.GenD.Analytic.NodalGreen
@[expose] public section
namespace CatalanMeasure.GenD.Analytic.GaussianEllipse
open GaussianHorner GaussianCertificate
noncomputable section

/-- The two integer square witnesses give a sharp Bernstein ellipse bound. -/
theorem ellipseH_castPair_div_le (v : ℤ × ℤ) (s um up : ℤ) (hs : 0 < s)
    (hm : 0 ≤ um) (hp : 0 ≤ up)
    (hmsq : (v.1-s)^2 + v.2^2 ≤ um^2)
    (hpsq : (v.1+s)^2 + v.2^2 ≤ up^2) :
    ellipseH (castPair v / (s : ℂ)) ≤ ((um : ℝ) + (up : ℝ)) / (2 * (s : ℝ)) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hminus := norm_castPair_le_of_square (a := (v.1-s,v.2)) hm hmsq
  have hplus := norm_castPair_le_of_square (a := (v.1+s,v.2)) hp hpsq
  have em : castPair v / (s : ℂ) - 1 = castPair (v.1-s,v.2) / (s : ℂ) := by
    simp only [castPair, Int.cast_sub, Int.cast_zero, zero_mul, add_zero]
    field_simp [hsC]
    apply Complex.ext <;> simp
  have ep : castPair v / (s : ℂ) + 1 = castPair (v.1+s,v.2) / (s : ℂ) := by
    simp only [castPair, Int.cast_add, Int.cast_zero, zero_mul, add_zero]
    field_simp [hsC]
    apply Complex.ext <;> simp
  have hsnorm : ‖(s : ℂ)‖ = (s : ℝ) := by rw [Complex.norm_intCast, abs_of_pos hsR]
  have hm' : ‖castPair v / (s : ℂ) - 1‖ ≤ (um : ℝ) / (s : ℝ) := by
    rw [em, norm_div, hsnorm]
    exact div_le_div_of_nonneg_right hminus hsR.le
  have hp' : ‖castPair v / (s : ℂ) + 1‖ ≤ (up : ℝ) / (s : ℝ) := by
    rw [ep, norm_div, hsnorm]
    exact div_le_div_of_nonneg_right hplus hsR.le
  unfold ellipseH
  calc
    _ ≤ ((um : ℝ) / (s : ℝ) + (up : ℝ) / (s : ℝ)) / 2 := by linarith
    _ = _ := by ring

end
end CatalanMeasure.GenD.Analytic.GaussianEllipse
#print axioms CatalanMeasure.GenD.Analytic.GaussianEllipse.ellipseH_castPair_div_le
