module

public import CatalanLambda.Cert.RayBox

@[expose] public section

/-!
# Upper bound of `Utau x y` over a box (`xhi < 0`, `0 ≤ ylo`), no `π` term

Extracted from the legacy `box_sound_g` proof (pieces (A), (B), (C)); `UbUp = 1 + Aup + Bup + Cup`.
-/

open Real

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Cert

set_option maxRecDepth 100000

def UbUp (xlo xhi ylo yhi : ℤ) : ℚ :=
  let L1 := L1Q xlo yhi
  let Aup : ℚ := (1 / 2) * qmax ((-(xhi : ℚ) / 2 ^ 40) * L1) ((-(xlo : ℚ) / 2 ^ 40) * L1)
  let l := lQ xhi ylo
  let Bup : ℚ := -(1 / 2) * qmin ((((2 : ℚ) ^ 40 - xhi) / 2 ^ 40) * l)
    ((((2 : ℚ) ^ 40 - xlo) / 2 ^ 40) * l)
  let th := thetaQ (vloQ xlo ylo yhi)
  let Cup : ℚ := -qmin ((ylo : ℚ) / 2 ^ 40 * th) ((yhi : ℚ) / 2 ^ 40 * th)
  1 + Aup + Bup + Cup

theorem utau_box_le (xlo xhi ylo yhi : ℤ)
    (hxhi : xhi < 0) (hxlohi : xlo ≤ xhi) (hylo : 0 ≤ ylo)
    (x y : ℝ)
    (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40)
    (hy1 : (ylo : ℝ) / 2 ^ 40 ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ 40) :
    CatalanLambda.Cert.Utau x y ≤ ((UbUp xlo xhi ylo yhi : ℚ) : ℝ) := by
  have hxhiR : (xhi : ℝ) ≤ -1 := by exact_mod_cast (by omega : xhi ≤ -1)
  have hxloR : (xlo : ℝ) ≤ -1 := by
    have : xlo ≤ -1 := by omega
    exact_mod_cast this
  have hyloR : (0 : ℝ) ≤ ylo := by exact_mod_cast hylo
  have hxneg : x < 0 := by
    have : x ≤ (xhi : ℝ) / 2 ^ 40 := hx2
    have h2 : (xhi : ℝ) / 2 ^ 40 < 0 := by
      apply div_neg_of_neg_of_pos <;> [linarith; positivity]
    linarith
  have hy0 : 0 ≤ y := by
    have : (0 : ℝ) ≤ (ylo : ℝ) / 2 ^ 40 := by positivity
    linarith
  have hp40 : (0 : ℝ) < 2 ^ 40 := by positivity
  -- (A)
  have hA : -x * (Real.log (x ^ 2 + y ^ 2) / 2) ≤
      (((1 / 2) * qmax ((-(xhi : ℚ) / 2 ^ 40) * L1Q xlo yhi)
        ((-(xlo : ℚ) / 2 ^ 40) * L1Q xlo yhi) : ℚ) : ℝ) := by
    have hN1 : 0 < (xlo * xlo + yhi * yhi).toNat := by
      have : 0 < xlo * xlo + yhi * yhi := by nlinarith
      omega
    have hN1c : (((xlo * xlo + yhi * yhi).toNat : ℕ) : ℝ) = (xlo : ℝ) * xlo + (yhi : ℝ) * yhi := by
      have : 0 ≤ xlo * xlo + yhi * yhi := by nlinarith
      have h := Int.toNat_of_nonneg this
      have h2 : (((xlo * xlo + yhi * yhi).toNat : ℕ) : ℤ) = xlo * xlo + yhi * yhi := h
      exact_mod_cast h2
    have hxsq : x ^ 2 ≤ ((xlo : ℝ) / 2 ^ 40) ^ 2 := by nlinarith
    have hysq : y ^ 2 ≤ ((yhi : ℝ) / 2 ^ 40) ^ 2 := by nlinarith
    have hpos : 0 < x ^ 2 + y ^ 2 := by nlinarith
    have hle : x ^ 2 + y ^ 2 ≤ (((xlo * xlo + yhi * yhi).toNat : ℕ) : ℝ) / 2 ^ 80 := by
      rw [hN1c]
      have : ((xlo : ℝ) / 2 ^ 40) ^ 2 + ((yhi : ℝ) / 2 ^ 40) ^ 2 =
          ((xlo : ℝ) * xlo + (yhi : ℝ) * yhi) / 2 ^ 80 := by ring
      linarith
    have hlog : Real.log (x ^ 2 + y ^ 2) ≤ (L1Q xlo yhi : ℝ) := by
      have := (Real.log_le_log hpos hle).trans (logUpS_spec hN1)
      unfold L1Q; push_cast; exact this
    set L1 : ℝ := (L1Q xlo yhi : ℝ) with hL1
    push_cast
    set a := -x with ha
    have ha0 : 0 ≤ a := by linarith
    have ha1 : -(xhi : ℝ) / 2 ^ 40 ≤ a := by
      rw [ha]; have : x ≤ (xhi : ℝ) / 2 ^ 40 := hx2; linarith [neg_div (2 ^ 40 : ℝ) (xhi : ℝ)]
    have ha2 : a ≤ -(xlo : ℝ) / 2 ^ 40 := by
      rw [ha]; have : (xlo : ℝ) / 2 ^ 40 ≤ x := hx1; linarith [neg_div (2 ^ 40 : ℝ) (xlo : ℝ)]
    have h1 : a * Real.log (x ^ 2 + y ^ 2) ≤ a * L1 := mul_le_mul_of_nonneg_left hlog ha0
    have h2 : a * L1 ≤ max ((-(xhi : ℝ) / 2 ^ 40) * L1) ((-(xlo : ℝ) / 2 ^ 40) * L1) := by
      rcases le_total 0 L1 with h | h
      · exact le_max_of_le_right (mul_le_mul_of_nonneg_right ha2 h)
      · exact le_max_of_le_left (mul_le_mul_of_nonpos_right ha1 h)
    have e : -x * (Real.log (x ^ 2 + y ^ 2) / 2) = a * Real.log (x ^ 2 + y ^ 2) / 2 := by
      rw [ha]; ring
    rw [e]
    linarith
  -- (B)
  have hB : -(1 / 2 : ℝ) * min (((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) * (lQ xhi ylo : ℝ))
        (((2 ^ 40 - (xlo : ℝ)) / 2 ^ 40) * (lQ xhi ylo : ℝ)) ≥
      -((1 - x) * (Real.log ((1 - x) ^ 2 + y ^ 2) / 2)) := by
    have hN2pos : 0 < (2 ^ 40 - xhi) ^ 2 + ylo ^ 2 := by nlinarith
    have hN2 : 0 < ((2 ^ 40 - xhi) ^ 2 + ylo ^ 2).toNat := by omega
    have hN2c : ((((2 ^ 40 - xhi) ^ 2 + ylo ^ 2).toNat : ℕ) : ℝ) =
        (2 ^ 40 - (xhi : ℝ)) ^ 2 + (ylo : ℝ) ^ 2 := by
      have h := Int.toNat_of_nonneg hN2pos.le
      have h2 : ((((2 ^ 40 - xhi) ^ 2 + ylo ^ 2).toNat : ℕ) : ℤ) = (2 ^ 40 - xhi) ^ 2 + ylo ^ 2 := h
      exact_mod_cast h2
    have hc1 : (2 ^ 40 - (xhi : ℝ)) / 2 ^ 40 ≤ 1 - x := by
      have : x ≤ (xhi : ℝ) / 2 ^ 40 := hx2
      have e : (2 ^ 40 - (xhi : ℝ)) / 2 ^ 40 = 1 - (xhi : ℝ) / 2 ^ 40 := by field_simp
      linarith
    have hc2 : 1 - x ≤ (2 ^ 40 - (xlo : ℝ)) / 2 ^ 40 := by
      have : (xlo : ℝ) / 2 ^ 40 ≤ x := hx1
      have e : (2 ^ 40 - (xlo : ℝ)) / 2 ^ 40 = 1 - (xlo : ℝ) / 2 ^ 40 := by field_simp
      linarith
    have hc0 : 0 < (2 ^ 40 - (xhi : ℝ)) / 2 ^ 40 := by
      apply div_pos _ hp40; linarith
    have hw : (((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) ^ 2 + ((ylo : ℝ) / 2 ^ 40) ^ 2) ≤
        (1 - x) ^ 2 + y ^ 2 := by
      have h1 : ((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) ^ 2 ≤ (1 - x) ^ 2 := by
        apply pow_le_pow_left₀ hc0.le hc1
      have h2 : ((ylo : ℝ) / 2 ^ 40) ^ 2 ≤ y ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) hy1
      linarith
    have hwe : ((((2 ^ 40 - xhi) ^ 2 + ylo ^ 2).toNat : ℕ) : ℝ) / 2 ^ 80 =
        ((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) ^ 2 + ((ylo : ℝ) / 2 ^ 40) ^ 2 := by
      rw [hN2c]; field_simp
    have hwpos : 0 < ((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) ^ 2 + ((ylo : ℝ) / 2 ^ 40) ^ 2 := by positivity
    have hlog : (lQ xhi ylo : ℝ) ≤ Real.log ((1 - x) ^ 2 + y ^ 2) := by
      have h1 := logLoS_spec hN2
      have h2 : Real.log ((((2 ^ 40 - xhi) ^ 2 + ylo ^ 2).toNat : ℝ) / 2 ^ 80) ≤
          Real.log ((1 - x) ^ 2 + y ^ 2) := by
        apply Real.log_le_log (by rw [hwe]; exact hwpos)
        rw [hwe]; exact hw
      unfold lQ; push_cast; exact h1.trans h2
    set l : ℝ := (lQ xhi ylo : ℝ) with hl
    set c := 1 - x with hc
    have hcpos : 0 < c := by linarith
    have h1 : c * l ≤ c * Real.log ((1 - x) ^ 2 + y ^ 2) := mul_le_mul_of_nonneg_left hlog hcpos.le
    have h2 : min (((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) * l) (((2 ^ 40 - (xlo : ℝ)) / 2 ^ 40) * l) ≤ c * l := by
      rcases le_total 0 l with h | h
      · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hc1 h)
      · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hc2 h)
    have e : -(c * (Real.log ((1 - x) ^ 2 + y ^ 2) / 2)) = -(c * Real.log ((1 - x) ^ 2 + y ^ 2)) / 2 := by
      ring
    rw [e]
    linarith
  -- (C)
  have hC : (-min ((ylo : ℝ) / 2 ^ 40 * (thetaQ (vloQ xlo ylo yhi) : ℝ))
        ((yhi : ℝ) / 2 ^ 40 * (thetaQ (vloQ xlo ylo yhi) : ℝ))) ≥
      -(y * Real.arctan (y / (x ^ 2 + y ^ 2 - x))) := by
    have hden : 0 < (xlo : ℝ) * xlo + yhi * yhi - xlo * 2 ^ 40 := by nlinarith
    have hv0 : 0 ≤ vloQ xlo ylo yhi := by
      unfold vloQ
      have : (0 : ℚ) < (xlo : ℚ) * xlo + yhi * yhi - xlo * 2 ^ 40 := by
        have h := hden
        exact_mod_cast h
      positivity
    have hvle : ((vloQ xlo ylo yhi : ℚ) : ℝ) ≤ y / (x ^ 2 + y ^ 2 - x) := by
      unfold vloQ
      push_cast
      have hd2 : 0 < x ^ 2 + y ^ 2 - x := by nlinarith
      rw [div_le_div_iff₀ hden hd2]
      -- ylo·Z·(x²+y²−x) ≤ y·(xlo²+yhi²−xlo·Z)
      have hxx : x ^ 2 - x ≤ ((xlo : ℝ) / 2 ^ 40) ^ 2 - (xlo : ℝ) / 2 ^ 40 := by nlinarith
      have hyy : y ^ 2 ≤ ((yhi : ℝ) / 2 ^ 40) ^ 2 := by nlinarith
      have hD : (x ^ 2 + y ^ 2 - x) * 2 ^ 80 ≤ (xlo : ℝ) * xlo + yhi * yhi - xlo * 2 ^ 40 := by
        have e : ((xlo : ℝ) * xlo + yhi * yhi - xlo * 2 ^ 40) =
            (((xlo : ℝ) / 2 ^ 40) ^ 2 + ((yhi : ℝ) / 2 ^ 40) ^ 2 - (xlo : ℝ) / 2 ^ 40) * 2 ^ 80 := by
          field_simp
        rw [e]; apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
      have hyl : (ylo : ℝ) * 2 ^ 40 ≤ y * 2 ^ 80 := by
        have : (ylo : ℝ) / 2 ^ 40 ≤ y := hy1
        have e : (ylo : ℝ) * 2 ^ 40 = (ylo : ℝ) / 2 ^ 40 * 2 ^ 80 := by field_simp
        rw [e]; exact mul_le_mul_of_nonneg_right this (by positivity)
      calc (ylo : ℝ) * 2 ^ 40 * (x ^ 2 + y ^ 2 - x)
          ≤ y * 2 ^ 80 * (x ^ 2 + y ^ 2 - x) :=
            mul_le_mul_of_nonneg_right hyl hd2.le
        _ = y * ((x ^ 2 + y ^ 2 - x) * 2 ^ 80) := by ring
        _ ≤ y * ((xlo : ℝ) * xlo + yhi * yhi - xlo * 2 ^ 40) :=
            mul_le_mul_of_nonneg_left hD hy0
    have hth := thetaQ_le_arctan hv0 hvle
    set th : ℝ := (thetaQ (vloQ xlo ylo yhi) : ℝ) with hth_def
    have h1 : y * th ≤ y * Real.arctan (y / (x ^ 2 + y ^ 2 - x)) :=
      mul_le_mul_of_nonneg_left hth hy0
    have h2 : min ((ylo : ℝ) / 2 ^ 40 * th) ((yhi : ℝ) / 2 ^ 40 * th) ≤ y * th := by
      rcases le_total 0 th with h | h
      · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hy1 h)
      · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hy2 h)
    linarith
  unfold CatalanLambda.Cert.Utau
  simp only [UbUp]
  have hA' := hA
  have hC' := hC
  push_cast at hA' hC' ⊢
  have hBc : -(1 / 2 : ℝ) * min (((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) * (lQ xhi ylo : ℝ))
        (((2 ^ 40 - (xlo : ℝ)) / 2 ^ 40) * (lQ xhi ylo : ℝ)) ≥
      -((1 - x) * (Real.log ((1 - x) ^ 2 + y ^ 2) / 2)) := hB
  linarith [hA', hBc, hC']

end CatalanCore.Cert.SigmaHyb
