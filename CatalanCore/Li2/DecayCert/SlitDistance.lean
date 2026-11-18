module
public import CatalanCore.Li2.DecayCert.Source
@[expose] public section
set_option Elab.async false
open Complex Set
open CatalanCore.Tools.Joukowski
namespace CatalanCore.Li2.DecayCert

def slitDistSq (ζ : CQ) : ℚ :=
  if ζ.1 < -1 then (ζ.1+1)^2+ζ.2^2
  else if 1 < ζ.1 then (ζ.1-1)^2+ζ.2^2 else ζ.2^2

theorem slitDistSq_nonneg (ζ : CQ) : 0 ≤ slitDistSq ζ := by
  unfold slitDistSq
  split_ifs <;> positivity

theorem slitDistSq_pos_iff (ζ : CQ) :
    0 < slitDistSq ζ ↔ ζ.1 < -1 ∨ 1 < ζ.1 ∨ ζ.2 ≠ 0 := by
  by_cases hl : ζ.1 < -1
  · simp only [slitDistSq,if_pos hl]
    constructor
    · intro _; exact Or.inl hl
    · intro _
      have hn : ζ.1+1 ≠ 0 := by linarith
      nlinarith [sq_pos_of_ne_zero hn, sq_nonneg ζ.2]
  · by_cases hr : 1 < ζ.1
    · simp only [slitDistSq,if_neg hl,if_pos hr]
      constructor
      · intro _; exact Or.inr (Or.inl hr)
      · intro _
        have hn : ζ.1-1 ≠ 0 := by linarith
        nlinarith [sq_pos_of_ne_zero hn, sq_nonneg ζ.2]
    · simp [slitDistSq,hl,hr,sq_pos_iff]

private theorem abs_re_le_jc (z : ℂ) : |z.re| ≤ jc z := by
  have h1 := Complex.abs_re_le_norm (z-1)
  have h2 := Complex.abs_re_le_norm (z+1)
  simp only [Complex.sub_re,Complex.add_re,Complex.one_re] at h1 h2
  have ha := abs_add_le (z.re-1) (z.re+1)
  have he : |(z.re-1)+(z.re+1)|=2*|z.re| := by
    rw [show (z.re-1)+(z.re+1)=2*z.re by ring, abs_mul]
    norm_num
  rw [he] at ha
  unfold jc
  linarith

private theorem one_lt_jc_im {z : ℂ} (hz : z.im ≠ 0) : 1 < jc z := by
  have h1 := Complex.abs_re_lt_norm.mpr (show (z-1).im ≠ 0 by simpa using hz)
  have h2 := Complex.abs_re_lt_norm.mpr (show (z+1).im ≠ 0 by simpa using hz)
  simp only [Complex.sub_re,Complex.add_re,Complex.one_re] at h1 h2
  have ha := abs_sub (z.re+1) (z.re-1)
  rw [show z.re+1-(z.re-1)=2 by ring] at ha
  norm_num at ha
  unfold jc
  linarith

theorem slitDistSq_pos_jc (ζ : CQ) (hζ : 0 < slitDistSq ζ) : 1 < jc (cqReal ζ) := by
  have hre : (cqReal ζ).re=(ζ.1:ℝ) := by norm_num [cqReal]
  have him : (cqReal ζ).im=(ζ.2:ℝ) := by norm_num [cqReal]
  rcases (slitDistSq_pos_iff ζ).mp hζ with hl | hr | hi
  · have hh : (cqReal ζ).re < -1 := by rw [hre]; exact_mod_cast hl
    have ha := abs_re_le_jc (cqReal ζ)
    rw [abs_of_neg (by linarith)] at ha
    linarith
  · have hh : 1 < (cqReal ζ).re := by rw [hre]; exact_mod_cast hr
    have ha := abs_re_le_jc (cqReal ζ)
    rw [abs_of_pos (by linarith)] at ha
    linarith
  · apply one_lt_jc_im
    rw [him]
    exact_mod_cast hi

#print axioms slitDistSq_nonneg
#print axioms slitDistSq_pos_iff
#print axioms slitDistSq_pos_jc
end CatalanCore.Li2.DecayCert
