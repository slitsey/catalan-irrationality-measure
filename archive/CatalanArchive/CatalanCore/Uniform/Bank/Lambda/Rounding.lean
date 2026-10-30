import CatalanCore.Uniform.Bank.Lambda.Geom
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore.Uniform.Content.Shape

/-- Exact trim rounding: the number of border pairs differs from r/10 by at most 1/2. -/
theorem FL_border_round {r : ℕ} (hr : r % 2 = 0) :
    10 * FL.borderSize r ≤ r + 5 ∧ r ≤ 10 * FL.borderSize r + 5 := by
  have hb : FL.borderSize r = min ⌈((1 / 5 : ℚ) * r) / 2⌉₊
      ⌈((1 / 5 : ℚ) * r - 1) / 2⌉₊ := altGeom_borderSize _ one_fifth_pos hr
  have hc : ⌈((1 / 5 : ℚ) * r - 1) / 2⌉₊ ≤ ⌈((1 / 5 : ℚ) * r) / 2⌉₊ :=
    Nat.ceil_le_ceil (by linarith)
  rw [min_eq_right hc] at hb
  rw [hb]
  by_cases h5 : 5 ≤ r
  · have h5q : (5 : ℚ) ≤ r := by exact_mod_cast h5
    have h0 : (0 : ℚ) ≤ ((1 / 5 : ℚ) * r - 1) / 2 := by linarith
    have hl := Nat.le_ceil (((1 / 5 : ℚ) * r - 1) / 2)
    have hu := Nat.ceil_lt_add_one h0
    constructor
    · have hq : (10 : ℚ) * (⌈((1 / 5 : ℚ) * r - 1) / 2⌉₊ : ℚ) ≤ r + 5 := by linarith
      exact_mod_cast hq
    · have hq : (r : ℚ) ≤ 10 * (⌈((1 / 5 : ℚ) * r - 1) / 2⌉₊ : ℚ) + 5 := by linarith
      exact_mod_cast hq
  · have hz : ⌈((1 / 5 : ℚ) * r - 1) / 2⌉₊ = 0 := by
      apply Nat.ceil_eq_zero.mpr
      have hq : (r : ℚ) < 5 := by exact_mod_cast (show r < 5 by omega)
      linarith
    rw [hz]
    omega

theorem FL_border_le_scale {r : ℕ} (hr : r % 2 = 0) : FL.borderSize r ≤ r := by
  have h := (FL_border_round hr).1
  omega

#print axioms FL_border_round
end CatalanCore.Uniform.Bank.Lambda
