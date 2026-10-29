import CatalanCore.Uniform.Bank.ThirdsContent.CovDefs
import CatalanCore.Uniform.Bank.ThirdsContent.TwoTerm
import CatalanCore.Uniform.Bank.ThirdsContent.Tbridge
set_option Elab.async false

/-! # Shared facts for the thirds piece covers (lane B, B4b)

* `cFr_thirdsAc`, `cFr_thirdsBc`: the crude-exponent constant is `23`.
* `border_bounds`: the border size `k` of the thirds geometry at even `r` satisfies
  `3 r <= 20 k + 10` and `20 k < 3 r + 10`.
* `hsq_of`: one level only (`3 (r + 2k) < p^2`) when `p > 3 r/1000` and `r >= 10^6`. -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.Shape
  CatalanFrames.Thirds

theorem den_13 : ((1 : ℚ) / 3).den = 3 := by
  have h := Rat.den_div_eq_of_coprime (a := 1) (b := 3) (by norm_num) (by norm_num)
  have e : (((1 : ℤ) : ℚ) / ((3 : ℤ) : ℚ)) = 1 / 3 := by norm_num
  rw [e] at h; exact_mod_cast h

theorem num_13 : ((1 : ℚ) / 3).num = 1 := by
  have h := Rat.num_div_eq_of_coprime (a := 1) (b := 3) (by norm_num) (by norm_num)
  have e : (((1 : ℤ) : ℚ) / ((3 : ℤ) : ℚ)) = 1 / 3 := by norm_num
  rw [e] at h; exact_mod_cast h

theorem den_23 : ((2 : ℚ) / 3).den = 3 := by
  have h := Rat.den_div_eq_of_coprime (a := 2) (b := 3) (by norm_num) (by norm_num)
  have e : (((2 : ℤ) : ℚ) / ((3 : ℤ) : ℚ)) = 2 / 3 := by norm_num
  rw [e] at h; exact_mod_cast h

theorem num_23 : ((2 : ℚ) / 3).num = 2 := by
  have h := Rat.num_div_eq_of_coprime (a := 2) (b := 3) (by norm_num) (by norm_num)
  have e : (((2 : ℤ) : ℚ) / ((3 : ℤ) : ℚ)) = 2 / 3 := by norm_num
  rw [e] at h; exact_mod_cast h

theorem cFr_thirdsAc : cFr thirdsAc = 23 := by
  have h : (thirdsAc.norm).num.toNat = 9 := by
    show ((9 : ℚ)).num.toNat = 9
    norm_num
  have h2 : Dc thirdsAc = 7 := by
    unfold Dc Dm
    show 1 + ∑ x : Fin 2, (((![(1 / 3 : ℚ), 1] x).den) + ((![(1 / 3 : ℚ), 1] x).num.toNat)) = 7
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, den_13, num_13, Rat.den_one, Rat.num_one]
    rfl
  unfold cFr
  rw [h, h2]

theorem cFr_thirdsBc : cFr thirdsBc = 25 := by
  have h : (thirdsBc.norm).num.toNat = 9 := by
    show ((9 : ℚ)).num.toNat = 9
    norm_num
  have h2 : Dc thirdsBc = 8 := by
    unfold Dc Dm
    show 1 + ∑ x : Fin 2, (((![(2 / 3 : ℚ), 1] x).den) + ((![(2 / 3 : ℚ), 1] x).num.toNat)) = 8
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, den_23, num_23, Rat.den_one, Rat.num_one]
    rfl
  unfold cFr
  rw [h, h2]

theorem border_bounds {r : ℕ} (hr : r % 2 = 0) :
    3 * r ≤ 20 * G310.borderSize r + 10 ∧ 20 * G310.borderSize r < 3 * r + 10 := by
  have hb : G310.borderSize r = min ⌈((3 / 10 : ℚ) * r) / 2⌉₊ ⌈((3 / 10 : ℚ) * r - 1) / 2⌉₊ :=
    altGeom_borderSize (3 / 10) c310_pos hr
  have hc : ⌈((3 / 10 : ℚ) * r - 1) / 2⌉₊ ≤ ⌈((3 / 10 : ℚ) * r) / 2⌉₊ :=
    Nat.ceil_le_ceil (by linarith)
  rw [min_eq_right hc] at hb
  rw [hb]
  set x : ℚ := ((3 / 10 : ℚ) * r - 1) / 2 with hx
  by_cases h0 : 0 ≤ x
  · have h1 := Nat.le_ceil x
    have h2 := Nat.ceil_lt_add_one h0
    have e : (20 : ℚ) * x = 3 * r - 10 := by rw [hx]; ring
    constructor
    · have : (3 : ℚ) * r ≤ 20 * (⌈x⌉₊ : ℚ) + 10 := by nlinarith
      exact_mod_cast this
    · have : (20 : ℚ) * (⌈x⌉₊ : ℚ) < 3 * r + 10 := by nlinarith
      exact_mod_cast this
  · have hneg : x < 0 := lt_of_not_ge h0
    have hz : ⌈x⌉₊ = 0 := Nat.ceil_eq_zero.2 hneg.le
    rw [hz]
    have e : (20 : ℚ) * x = 3 * r - 10 := by rw [hx]; ring
    have : (3 : ℚ) * r < 10 := by nlinarith
    constructor
    · have : 3 * r < 10 := by exact_mod_cast this
      omega
    · omega

theorem hsq_of {r p k : ℕ} (hr : 10 ^ 6 ≤ r) (hk : 20 * k < 3 * r + 10) (hp : 3 * r < 1000 * p) :
    3 * (r + 2 * k) < p * p := by
  have h1 : 1000 * p ≥ 3 * r + 1 := hp
  have h2 : (1000 * p) * (1000 * p) ≥ (3 * r + 1) * (3 * r + 1) := Nat.mul_le_mul h1 h1
  nlinarith

end CatalanCore.Uniform.Bank.ThirdsContent
