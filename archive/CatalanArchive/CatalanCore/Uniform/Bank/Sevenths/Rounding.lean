import CatalanCore.Uniform.Bank.Sevenths.Geom
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore.Uniform.Content.Shape

/-- Exact trim rounding: the number of border pairs differs from r/12 by at most 1/2. -/
theorem F7_border_round {r : ℕ} (hr : r % 2 = 0) :
    12 * F7.borderSize r ≤ r + 6 ∧ r ≤ 12 * F7.borderSize r + 6 := by
  have hb : F7.borderSize r = min ⌈((1 / 6 : ℚ) * r) / 2⌉₊
      ⌈((1 / 6 : ℚ) * r - 1) / 2⌉₊ := altGeom_borderSize _ one_sixth_pos hr
  have hc : ⌈((1 / 6 : ℚ) * r - 1) / 2⌉₊ ≤ ⌈((1 / 6 : ℚ) * r) / 2⌉₊ :=
    Nat.ceil_le_ceil (by linarith)
  rw [min_eq_right hc] at hb
  rw [hb]
  by_cases h5 : 6 ≤ r
  · have h5q : (6 : ℚ) ≤ r := by exact_mod_cast h5
    have h0 : (0 : ℚ) ≤ ((1 / 6 : ℚ) * r - 1) / 2 := by linarith
    have hl := Nat.le_ceil (((1 / 6 : ℚ) * r - 1) / 2)
    have hu := Nat.ceil_lt_add_one h0
    constructor
    · have hq : (12 : ℚ) * (⌈((1 / 6 : ℚ) * r - 1) / 2⌉₊ : ℚ) ≤ r + 6 := by linarith
      exact_mod_cast hq
    · have hq : (r : ℚ) ≤ 12 * (⌈((1 / 6 : ℚ) * r - 1) / 2⌉₊ : ℚ) + 6 := by linarith
      exact_mod_cast hq
  · have hz : ⌈((1 / 6 : ℚ) * r - 1) / 2⌉₊ = 0 := by
      apply Nat.ceil_eq_zero.mpr
      have hq : (r : ℚ) < 6 := by exact_mod_cast (show r < 6 by omega)
      linarith
    rw [hz]
    omega

theorem F7_border_le_scale {r : ℕ} (hr : r % 2 = 0) : F7.borderSize r ≤ r := by
  have h := (F7_border_round hr).1
  omega

theorem F7_border_upper_strict {r : ℕ} (hr : r % 2 = 0) :
    12 * F7.borderSize r < r + 6 := by
  have hb : F7.borderSize r = min ⌈((1 / 6 : ℚ) * r) / 2⌉₊
      ⌈((1 / 6 : ℚ) * r - 1) / 2⌉₊ := altGeom_borderSize _ one_sixth_pos hr
  have hc : ⌈((1 / 6 : ℚ) * r - 1) / 2⌉₊ ≤ ⌈((1 / 6 : ℚ) * r) / 2⌉₊ :=
    Nat.ceil_le_ceil (by linarith)
  rw [min_eq_right hc] at hb
  rw [hb]
  by_cases h6 : 6 ≤ r
  · have h6q : (6 : ℚ) ≤ r := by exact_mod_cast h6
    have h0 : (0 : ℚ) ≤ ((1 / 6 : ℚ) * r - 1) / 2 := by linarith
    have hu := Nat.ceil_lt_add_one h0
    have hq : (12 : ℚ) * (⌈((1 / 6 : ℚ) * r - 1) / 2⌉₊ : ℚ) < r + 6 := by linarith
    exact_mod_cast hq
  · have hz : ⌈((1 / 6 : ℚ) * r - 1) / 2⌉₊ = 0 := by
      apply Nat.ceil_eq_zero.mpr
      have hq : (r : ℚ) < 6 := by exact_mod_cast (show r < 6 by omega)
      linarith
    rw [hz]
    omega

theorem F7_border_twice_le {r p : ℕ} (hr : r % 2 = 0) (hrp : r ≤ 6 * p) :
    2 * F7.borderSize r ≤ p := by
  have h := F7_border_upper_strict hr
  omega

theorem F7_border_pos {r : ℕ} (hr : r % 2 = 0) (hr12 : 12 ≤ r) :
    1 ≤ F7.borderSize r := by
  have h := (F7_border_round hr).2
  omega

#print axioms F7_border_round
end CatalanCore.Uniform.Bank.Sevenths
