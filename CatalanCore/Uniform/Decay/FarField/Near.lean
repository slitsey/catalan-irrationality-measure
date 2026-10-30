module

public import CatalanCore.Uniform.Decay.FarField.Taylor
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Field.Basic

@[expose] public section
set_option Elab.async false

/-!
# Linearisation of a finite multipole sum about a point (lane D, package D15)

For coefficients `ν_k`, a base point `u0` and a displacement `η` with `‖η‖/‖u0‖ ≤ a < 1`:
`∑_k ν_k / ((k+1) (u0+η)^(k+1))` equals `∑_k ν_k w^(k+1)/(k+1) - η ∑_k ν_k w^(k+2)` (with `w = 1/u0`)
up to `a² ∑_k ‖ν_k‖ tb a (k+1) / ((k+1) rm^(k+1))`.
-/

namespace CatalanCore.Uniform.Decay.FarField

open Finset

theorem term_expand (ν u0 η : ℂ) (hu0 : u0 ≠ 0) (m : ℕ) (hm : m ≠ 0) (hx : η * u0⁻¹ ≠ -1) :
    ν / ((m : ℂ) * (u0 + η) ^ m)
      = ν * u0⁻¹ ^ m / (m : ℂ) - ν * u0⁻¹ ^ (m + 1) * η
        + ν * u0⁻¹ ^ m * (((1 + η * u0⁻¹) ^ m)⁻¹ - 1 + (m : ℂ) * (η * u0⁻¹)) / (m : ℂ) := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have h1 : 1 + η * u0⁻¹ ≠ 0 := by
    intro h; apply hx; linear_combination h
  have hfac : u0 + η = u0 * (1 + η * u0⁻¹) := by field_simp
  have ha : u0 ^ m ≠ 0 := pow_ne_zero m hu0
  have hb : (1 + η * u0⁻¹) ^ m ≠ 0 := pow_ne_zero m h1
  have e1 : ν / ((m : ℂ) * (u0 + η) ^ m)
      = ν * u0⁻¹ ^ m * ((1 + η * u0⁻¹) ^ m)⁻¹ / (m : ℂ) := by
    rw [hfac, mul_pow, inv_pow]
    field_simp
  rw [e1, pow_succ u0⁻¹ m]
  generalize ((1 + η * u0⁻¹) ^ m)⁻¹ = y
  generalize u0⁻¹ ^ m = W
  field_simp
  ring

theorem near_sum_bound (J : ℕ) (ν : ℕ → ℂ) (nb : ℕ → ℝ) (u0 η : ℂ) (rm vr : ℚ)
    (hrm : 0 < rm) (hu0 : (rm : ℝ) ≤ ‖u0‖) (hη : ‖η‖ ≤ (vr : ℝ)) (hvr : vr < rm)
    (hnb : ∀ k < J, ‖ν k‖ ≤ nb k) :
    |(∑ k ∈ range J, ν k / (((k + 1 : ℕ) : ℂ) * (u0 + η) ^ (k + 1))).re
        - (∑ k ∈ range J, ν k * u0⁻¹ ^ (k + 1) / ((k + 1 : ℕ) : ℂ)).re
        + ((∑ k ∈ range J, ν k * u0⁻¹ ^ (k + 2)) * η).re|
      ≤ (∑ k ∈ range J, nb k / (((k + 1 : ℕ) : ℝ) * (rm : ℝ) ^ (k + 1)) * (tb (vr / rm) (k + 1) : ℝ))
        * ((vr / rm : ℚ) : ℝ) ^ 2 := by
  have hrmR : (0 : ℝ) < rm := by exact_mod_cast hrm
  have hnu0 : 0 < ‖u0‖ := lt_of_lt_of_le hrmR hu0
  have hu : u0 ≠ 0 := norm_pos_iff.1 hnu0
  set a : ℚ := vr / rm with ha_def
  have ha1 : a < 1 := by rw [ha_def, div_lt_one hrm]; exact hvr
  set x : ℂ := η * u0⁻¹ with hx_def
  have hxa : ‖x‖ ≤ (a : ℝ) := by
    rw [hx_def, norm_mul, norm_inv, ha_def]
    push_cast
    have hvrR : ‖η‖ ≤ (vr : ℝ) := hη
    calc ‖η‖ * ‖u0‖⁻¹ ≤ (vr : ℝ) * (rm : ℝ)⁻¹ := by
          apply mul_le_mul hvrR _ (by positivity) (by
            have : 0 ≤ ‖η‖ := norm_nonneg _
            exact this.trans hvrR)
          exact inv_anti₀ hrmR hu0
      _ = (vr : ℝ) / rm := by rw [div_eq_mul_inv]
  have hx1 : ‖x‖ < 1 := lt_of_le_of_lt hxa (by exact_mod_cast ha1)
  have hxne : x ≠ -1 := by
    intro h; rw [h] at hx1; simp at hx1
  have hpt : ∀ k ∈ range J,
      ν k / (((k + 1 : ℕ) : ℂ) * (u0 + η) ^ (k + 1))
        - ν k * u0⁻¹ ^ (k + 1) / ((k + 1 : ℕ) : ℂ) + ν k * u0⁻¹ ^ (k + 2) * η
        = ν k * u0⁻¹ ^ (k + 1) * (((1 + x) ^ (k + 1))⁻¹ - 1 + ((k + 1 : ℕ) : ℂ) * x)
            / ((k + 1 : ℕ) : ℂ) := by
    intro k _
    have := term_expand (ν k) u0 η hu (k + 1) (Nat.succ_ne_zero k) hxne
    rw [hx_def] at *
    linear_combination this
  have hsum : (∑ k ∈ range J, ν k / (((k + 1 : ℕ) : ℂ) * (u0 + η) ^ (k + 1)))
        - (∑ k ∈ range J, ν k * u0⁻¹ ^ (k + 1) / ((k + 1 : ℕ) : ℂ))
        + (∑ k ∈ range J, ν k * u0⁻¹ ^ (k + 2)) * η
      = ∑ k ∈ range J, ν k * u0⁻¹ ^ (k + 1) * (((1 + x) ^ (k + 1))⁻¹ - 1 + ((k + 1 : ℕ) : ℂ) * x)
            / ((k + 1 : ℕ) : ℂ) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hpt
  have hre : (∑ k ∈ range J, ν k / (((k + 1 : ℕ) : ℂ) * (u0 + η) ^ (k + 1))).re
        - (∑ k ∈ range J, ν k * u0⁻¹ ^ (k + 1) / ((k + 1 : ℕ) : ℂ)).re
        + ((∑ k ∈ range J, ν k * u0⁻¹ ^ (k + 2)) * η).re
      = (∑ k ∈ range J, ν k * u0⁻¹ ^ (k + 1) * (((1 + x) ^ (k + 1))⁻¹ - 1 + ((k + 1 : ℕ) : ℂ) * x)
            / ((k + 1 : ℕ) : ℂ)).re := by
    rw [← hsum]; simp
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk' : k < J := Finset.mem_range.1 hk
  have he := inv_pow_taylor hxa ha1 (k + 1)
  have hw : ‖u0⁻¹‖ ≤ (rm : ℝ)⁻¹ := by
    rw [norm_inv]; exact inv_anti₀ hrmR hu0
  have hwk : ‖u0⁻¹ ^ (k + 1)‖ ≤ ((rm : ℝ)⁻¹) ^ (k + 1) := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hw _
  have hmk : ‖((k + 1 : ℕ) : ℂ)‖ = ((k + 1 : ℕ) : ℝ) := Complex.norm_natCast _
  have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [norm_div, norm_mul, norm_mul, hmk]
  have hx2 : ‖x‖ ^ 2 ≤ ((a : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxa 2
  have hTb : (0 : ℝ) ≤ (tb a (k + 1) : ℝ) := by exact_mod_cast tb_nonneg ha1 (k + 1)
  have hE : ‖((1 + x) ^ (k + 1))⁻¹ - 1 + ((k + 1 : ℕ) : ℂ) * x‖ ≤ (tb a (k + 1) : ℝ) * (a : ℝ) ^ 2 :=
    he.trans (mul_le_mul_of_nonneg_left hx2 hTb)
  have hnbk := hnb k hk'
  have hrinv : ((rm : ℝ)⁻¹) ^ (k + 1) = 1 / (rm : ℝ) ^ (k + 1) := by rw [inv_pow, one_div]
  rw [div_le_iff₀ hpos]
  calc ‖ν k‖ * ‖u0⁻¹ ^ (k + 1)‖ * ‖((1 + x) ^ (k + 1))⁻¹ - 1 + ((k + 1 : ℕ) : ℂ) * x‖
      ≤ nb k * ((rm : ℝ)⁻¹) ^ (k + 1) * ((tb a (k + 1) : ℝ) * (a : ℝ) ^ 2) := by
        apply mul_le_mul (mul_le_mul hnbk hwk (norm_nonneg _) ((norm_nonneg _).trans hnbk)) hE
          (norm_nonneg _) (by
            have := (norm_nonneg (ν k)).trans hnbk
            positivity)
    _ = nb k / (((k + 1 : ℕ) : ℝ) * (rm : ℝ) ^ (k + 1)) * (tb a (k + 1) : ℝ) * (a : ℝ) ^ 2
          * ((k + 1 : ℕ) : ℝ) := by
        rw [hrinv]; field_simp

end CatalanCore.Uniform.Decay.FarField
