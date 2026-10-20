module

public import CatalanCore.Cert.SigmaQuarter.Potential
public import CatalanCore.Cert.SigmaP6.Bridge

@[expose] public section

/-! Direct quarter-border bounds reuse the square checker with the empty atom
list. Its two field terms add to exactly the required field term. -/

open Real

namespace CatalanCore.Cert.SigmaQuarter

open CatalanLambda.Cert
open CatalanCore.Cert.SigmaP6

def logThreeHalfLo : ℚ := (logLoS (3 * 2 ^ 79) : ℚ) / 2 ^ 64

theorem logThreeHalfLo_le : (logThreeHalfLo : ℝ) ≤ Real.log (3 / 2) := by
  have h := logLoS_spec (N := 3 * 2 ^ 79) (by norm_num)
  unfold logThreeHalfLo
  push_cast
  norm_num at h ⊢
  exact h

noncomputable def gQuarter (pts : List Pt) (x y : ℝ) : ℝ :=
  (5 / 4) * Usig pts x y - (1 / 2) * Utau x y -
    (3 / 4) * Utau (2 * x / 3) (2 * y / 3) +
    (3 / 4) * Real.log (3 / 2) + (999 / 1000) * Real.pi * y

def quarterBoxLB (Ls : ℚ) (xl xh yl yh al ah bl bh : ℤ) : ℚ :=
  (5 / 4) * Ls + (1 / 2) * boxLBg 0 xl xh yl yh +
    (3 / 4) * boxLBg 0 al ah bl bh + (3 / 4) * logThreeHalfLo

theorem quarterBox_sound (pts : List Pt) (Ls : ℚ)
    (xl xh yl yh al ah bl bh : ℤ)
    (hx : xh < 0) (hxx : xl ≤ xh) (hy : 0 ≤ yl)
    (ha : ah < 0) (haa : al ≤ ah) (hb : 0 ≤ bl)
    (h1 : (al : ℚ) ≤ 2 * xl / 3) (h2 : 2 * (xh : ℚ) / 3 ≤ ah)
    (h3 : (bl : ℚ) ≤ 2 * yl / 3) (h4 : 2 * (yh : ℚ) / 3 ≤ bh)
    (x y : ℝ) (hx1 : (xl : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xh : ℝ) / 2 ^ 40)
    (hy1 : (yl : ℝ) / 2 ^ 40 ≤ y) (hy2 : y ≤ (yh : ℝ) / 2 ^ 40)
    (hS : (Ls : ℝ) ≤ Usig pts x y) :
    (quarterBoxLB Ls xl xh yl yh al ah bl bh : ℝ) ≤ gQuarter pts x y := by
  have h1r : (al : ℝ) ≤ 2 * xl / 3 := by exact_mod_cast h1
  have h2r : 2 * (xh : ℝ) / 3 ≤ ah := by exact_mod_cast h2
  have h3r : (bl : ℝ) ≤ 2 * yl / 3 := by exact_mod_cast h3
  have h4r : 2 * (yh : ℝ) / 3 ≤ bh := by exact_mod_cast h4
  have ha1 : (al : ℝ) / 2 ^ 40 ≤ 2 * x / 3 := by linarith
  have ha2 : 2 * x / 3 ≤ (ah : ℝ) / 2 ^ 40 := by linarith
  have hb1 : (bl : ℝ) / 2 ^ 40 ≤ 2 * y / 3 := by linarith
  have hb2 : 2 * y / 3 ≤ (bh : ℝ) / 2 ^ 40 := by linarith
  have hs1 := box_sound_g [] 0 (boxLBg 0 xl xh yl yh) xl xh yl yh hx hxx hy le_rfl
    x y hx1 hx2 hy1 hy2 (by simp [Usig])
  have hs2 := box_sound_g [] 0 (boxLBg 0 al ah bl bh) al ah bl bh ha haa hb le_rfl
    (2 * x / 3) (2 * y / 3) ha1 ha2 hb1 hb2 (by simp [Usig])
  simp only [gfun, Usig, zero_sub] at hs1 hs2
  unfold quarterBoxLB gQuarter
  push_cast
  nlinarith [logThreeHalfLo_le]

def quarterAxisLB (Ls : ℚ) (u1 u2 : ℚ) : ℚ :=
  (5 / 4) * Ls - (1 / 2) * u1 - (3 / 4) * u2 + (3 / 4) * logThreeHalfLo

theorem quarterAxis_sound (pts : List Pt) (Ls u1 u2 : ℚ) (x : ℝ)
    (hS : (Ls : ℝ) ≤ Usig pts x 0) (h1 : Utau x 0 ≤ (u1 : ℝ))
    (h2 : Utau (2 * x / 3) 0 ≤ (u2 : ℝ)) :
    (quarterAxisLB Ls u1 u2 : ℝ) ≤ gQuarter pts x 0 := by
  unfold quarterAxisLB gQuarter
  push_cast
  simp only [mul_zero, zero_div, add_zero]
  linarith [logThreeHalfLo_le]

end CatalanCore.Cert.SigmaQuarter
