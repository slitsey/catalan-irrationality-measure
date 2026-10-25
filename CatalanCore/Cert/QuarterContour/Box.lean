module

public import CatalanCore.Cert.SigmaQuarter.Box

@[expose] public section

open Real
namespace CatalanCore.Cert.QuarterContour
open CatalanLambda.Cert CatalanCore.Cert.SigmaP6

/-- The positive field slack is a certificate parameter. -/
noncomputable def gQuarter (epsilon : ℚ) (pts : List Pt) (x y : ℝ) : ℝ :=
  (5 / 4) * Usig pts x y - (1 / 2) * Utau x y -
    (3 / 4) * Utau (2 * x / 3) (2 * y / 3) +
    (3 / 4) * Real.log (3 / 2) + (1 - (epsilon : ℝ)) * Real.pi * y

/-- Transfer the old checker with a checked nonnegative field correction. -/
def quarterBoxLB (epsilon Ls : ℚ) (xl xh yl yh al ah bl bh : ℤ) : ℚ :=
  SigmaQuarter.quarterBoxLB Ls xl xh yl yh al ah bl bh +
    (1 / 1000 - epsilon) * PILO * ((yl : ℚ) / 2 ^ 40)

lemma gQuarter_eq (epsilon : ℚ) (pts : List Pt) (x y : ℝ) :
    gQuarter epsilon pts x y = SigmaQuarter.gQuarter pts x y +
      ((1 / 1000 : ℝ) - epsilon) * Real.pi * y := by
  unfold gQuarter SigmaQuarter.gQuarter
  ring

lemma correction_le {epsilon : ℚ} (he : epsilon ≤ 1 / 1000)
    (yl : ℤ) (hy : 0 ≤ yl) (y : ℝ) (hyl : (yl : ℝ) / 2 ^ 40 ≤ y) :
    (((1 / 1000 - epsilon) * PILO * ((yl : ℚ) / 2 ^ 40) : ℚ) : ℝ) ≤
      ((1 / 1000 : ℝ) - epsilon) * Real.pi * y := by
  have he' : (epsilon : ℝ) ≤ ((1 / 1000 : ℚ) : ℝ) := Rat.cast_le.mpr he
  have hd : (0 : ℝ) ≤ (1 / 1000 : ℝ) - epsilon := by norm_num at he'; linarith
  have hlo : (0 : ℝ) ≤ (yl : ℝ) / 2 ^ 40 := by positivity
  have hpi : (PILO : ℝ) * ((yl : ℝ) / 2 ^ 40) ≤ Real.pi * y :=
    (mul_le_mul_of_nonneg_right PILO_lt.le hlo).trans
      (mul_le_mul_of_nonneg_left hyl Real.pi_pos.le)
  have h := mul_le_mul_of_nonneg_left hpi hd
  push_cast at h ⊢
  nlinarith [h]

theorem quarterBox_sound (epsilon : ℚ) (he : epsilon ≤ 1 / 1000)
    (pts : List Pt) (Ls : ℚ) (xl xh yl yh al ah bl bh : ℤ)
    (hx : xh < 0) (hxx : xl ≤ xh) (hy : 0 ≤ yl)
    (ha : ah < 0) (haa : al ≤ ah) (hb : 0 ≤ bl)
    (h1 : (al : ℚ) ≤ 2 * xl / 3) (h2 : 2 * (xh : ℚ) / 3 ≤ ah)
    (h3 : (bl : ℚ) ≤ 2 * yl / 3) (h4 : 2 * (yh : ℚ) / 3 ≤ bh)
    (x y : ℝ) (hx1 : (xl : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xh : ℝ) / 2 ^ 40)
    (hy1 : (yl : ℝ) / 2 ^ 40 ≤ y) (hy2 : y ≤ (yh : ℝ) / 2 ^ 40)
    (hS : (Ls : ℝ) ≤ Usig pts x y) :
    (quarterBoxLB epsilon Ls xl xh yl yh al ah bl bh : ℝ) ≤ gQuarter epsilon pts x y := by
  have ho := SigmaQuarter.quarterBox_sound pts Ls xl xh yl yh al ah bl bh
    hx hxx hy ha haa hb h1 h2 h3 h4 x y hx1 hx2 hy1 hy2 hS
  have hc := correction_le he yl hy y hy1
  rw [gQuarter_eq]
  unfold quarterBoxLB
  push_cast at hc ⊢
  linarith

theorem quarterAxis_sound (epsilon : ℚ) (pts : List Pt) (Ls u1 u2 : ℚ) (x : ℝ)
    (hS : (Ls : ℝ) ≤ Usig pts x 0) (h1 : Utau x 0 ≤ (u1 : ℝ))
    (h2 : Utau (2 * x / 3) 0 ≤ (u2 : ℝ)) :
    (SigmaQuarter.quarterAxisLB Ls u1 u2 : ℝ) ≤ gQuarter epsilon pts x 0 := by
  rw [gQuarter_eq]
  simpa using SigmaQuarter.quarterAxis_sound pts Ls u1 u2 x hS h1 h2

end CatalanCore.Cert.QuarterContour
#print axioms CatalanCore.Cert.QuarterContour.quarterBox_sound
#print axioms CatalanCore.Cert.QuarterContour.quarterAxis_sound
