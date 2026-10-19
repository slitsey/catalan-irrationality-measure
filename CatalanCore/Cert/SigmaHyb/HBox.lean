module

public import CatalanCore.Cert.SigmaHyb.UexForm

@[expose] public section

/-!
# Hybrid box bounds

`UexR x y = (1/8) Utau (4x-4) (4y) + (1/4) log 2` is `U^{ex}_{1/4}` in real coordinates (`UexForm`).
* `UexUp` : rational upper bound of `UexR` over an integer box (scale `2^-40`), `xhi < 0`.
* `box_sound_H` : `mp ≤ boxLBg Ls … - UexUp …` and `Ls ≤ Usig pts` give `mp ≤ gfun pts - UexR`
  (the hybrid `g_h = (1+α)U^σ - U^τ - U^ex + field` in list form).
* `hbox_sound` : `thr ≤ Ls - UexUp …` and `Ls ≤ Usig pts` give `thr ≤ Usig pts - UexR`
  (the correction `h = U^λ - U^ex`).
-/

open Real

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Cert

set_option maxRecDepth 100000

noncomputable def UexR (x y : ℝ) : ℝ :=
  (1 / 8) * CatalanLambda.Cert.Utau (4 * x - 4) (4 * y) + (1 / 4) * Real.log 2

def L2UP : ℚ := 6931471808 / 10 ^ 10

lemma log2_le : Real.log 2 ≤ (L2UP : ℝ) := by
  have := Real.log_two_lt_d9
  have e : (L2UP : ℝ) = 0.6931471808 := by unfold L2UP; push_cast; norm_num
  rw [e]; exact this.le

def UexUp (xlo xhi ylo yhi : ℤ) : ℚ :=
  (1 / 8) * UbUp (4 * xlo - 2 ^ 42) (4 * xhi - 2 ^ 42) (4 * ylo) (4 * yhi) + L2UP / 4

theorem uexR_le (xlo xhi ylo yhi : ℤ) (hxhi : xhi < 0) (hxlohi : xlo ≤ xhi) (hylo : 0 ≤ ylo)
    (x y : ℝ) (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40)
    (hy1 : (ylo : ℝ) / 2 ^ 40 ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ 40) :
    UexR x y ≤ ((UexUp xlo xhi ylo yhi : ℚ) : ℝ) := by
  have h40 : (2 : ℝ) ^ 40 = 1099511627776 := by norm_num
  have hx1' : (xlo : ℝ) ≤ x * 1099511627776 := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 40)).1 hx1; rw [h40] at this; exact this
  have hx2' : x * 1099511627776 ≤ xhi := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 40)).1 hx2; rw [h40] at this; exact this
  have hy1' : (ylo : ℝ) ≤ y * 1099511627776 := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 40)).1 hy1; rw [h40] at this; exact this
  have hy2' : y * 1099511627776 ≤ yhi := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 40)).1 hy2; rw [h40] at this; exact this
  have key := utau_box_le (4 * xlo - 2 ^ 42) (4 * xhi - 2 ^ 42) (4 * ylo) (4 * yhi)
    (by omega) (by omega) (by omega) (4 * x - 4) (4 * y)
    (by push_cast; rw [h40, div_le_iff₀ (by norm_num)]; linarith)
    (by push_cast; rw [h40, le_div_iff₀ (by norm_num)]; linarith)
    (by push_cast; rw [h40, div_le_iff₀ (by norm_num)]; linarith)
    (by push_cast; rw [h40, le_div_iff₀ (by norm_num)]; linarith)
  unfold UexR UexUp
  push_cast
  have := log2_le
  push_cast at key
  nlinarith [key, this]

noncomputable def gHR (pts : List Pt) (x y : ℝ) : ℝ := gfun pts x y - UexR x y

def boxLBH (Ls : ℚ) (xlo xhi ylo yhi : ℤ) : ℚ := boxLBg Ls xlo xhi ylo yhi - UexUp xlo xhi ylo yhi

theorem box_sound_H (pts : List Pt) (Ls mp : ℚ) (xlo xhi ylo yhi : ℤ)
    (hxhi : xhi < 0) (hxlohi : xlo ≤ xhi) (hylo : 0 ≤ ylo)
    (hchk : mp ≤ boxLBH Ls xlo xhi ylo yhi) (x y : ℝ)
    (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40)
    (hy1 : (ylo : ℝ) / 2 ^ 40 ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ 40)
    (hS : (Ls : ℝ) ≤ Usig pts x y) :
    (mp : ℝ) ≤ gHR pts x y := by
  have h1 := box_sound_g pts Ls (mp + UexUp xlo xhi ylo yhi) xlo xhi ylo yhi hxhi hxlohi hylo
    (by unfold boxLBH at hchk; linarith) x y hx1 hx2 hy1 hy2 hS
  have h2 := uexR_le xlo xhi ylo yhi hxhi hxlohi hylo x y hx1 hx2 hy1 hy2
  unfold gHR
  push_cast at h1
  linarith

theorem hbox_sound (pts : List Pt) (Ls thr : ℚ) (xlo xhi ylo yhi : ℤ)
    (hxhi : xhi < 0) (hxlohi : xlo ≤ xhi) (hylo : 0 ≤ ylo)
    (hchk : thr ≤ Ls - UexUp xlo xhi ylo yhi) (x y : ℝ)
    (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40)
    (hy1 : (ylo : ℝ) / 2 ^ 40 ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ 40)
    (hS : (Ls : ℝ) ≤ Usig pts x y) :
    (thr : ℝ) ≤ Usig pts x y - UexR x y := by
  have h2 := uexR_le xlo xhi ylo yhi hxhi hxlohi hylo x y hx1 hx2 hy1 hy2
  have hc : (thr : ℝ) ≤ (Ls : ℝ) - (UexUp xlo xhi ylo yhi : ℝ) := by exact_mod_cast hchk
  linarith

end CatalanCore.Cert.SigmaHyb
