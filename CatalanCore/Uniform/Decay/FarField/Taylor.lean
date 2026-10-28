import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
set_option Elab.async false

/-!
# First-order expansion of `(1 + x)^(-k)` (lane D, package D15)

`‖(1+x)^(-k) - 1 + k x‖ ≤ tb a k ‖x‖²` for `‖x‖ ≤ a < 1`, with the explicit recursion
`tb a 0 = 0`, `tb a (k+1) = (tb a k + k + 1) / (1 - a)`.  Purely algebraic (no derivatives).
-/

namespace CatalanCore.Uniform.Decay.FarField

/-- The constant of the first-order expansion. -/
def tb (a : ℚ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => (tb a k + (k + 1)) / (1 - a)

theorem tb_nonneg {a : ℚ} (ha : a < 1) : ∀ k, 0 ≤ tb a k
  | 0 => le_refl _
  | k + 1 => by
    have := tb_nonneg ha k
    have h1 : 0 < 1 - a := by linarith
    simp only [tb]
    positivity

theorem inv_pow_taylor {x : ℂ} {a : ℚ} (hx : ‖x‖ ≤ (a : ℝ)) (ha : a < 1) (k : ℕ) :
    ‖((1 + x) ^ k)⁻¹ - 1 + (k : ℂ) * x‖ ≤ (tb a k : ℝ) * ‖x‖ ^ 2 := by
  have haR : (a : ℝ) < 1 := by exact_mod_cast ha
  have hx1 : ‖x‖ < 1 := lt_of_le_of_lt hx haR
  have hne : (1 + x) ≠ 0 := by
    intro h
    have : x = -1 := by linear_combination h
    rw [this] at hx1; simp at hx1
  have hlow : 1 - (a : ℝ) ≤ ‖1 + x‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-x)
    rw [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  induction k with
  | zero => simp [tb]
  | succ k ih =>
    have e : ((1 + x) ^ (k + 1))⁻¹ - 1 + ((k + 1 : ℕ) : ℂ) * x
        = (((1 + x) ^ k)⁻¹ - 1 + (k : ℂ) * x + ((k : ℂ) + 1) * x ^ 2) / (1 + x) := by
      push_cast
      field_simp
      ring
    rw [e, norm_div]
    have hpos : 0 < 1 - (a : ℝ) := by linarith
    have h1 : ‖((1 + x) ^ k)⁻¹ - 1 + (k : ℂ) * x + ((k : ℂ) + 1) * x ^ 2‖
        ≤ ((tb a k : ℝ) + (k + 1)) * ‖x‖ ^ 2 := by
      refine (norm_add_le _ _).trans ?_
      have h2 : ‖((k : ℂ) + 1) * x ^ 2‖ = ((k : ℝ) + 1) * ‖x‖ ^ 2 := by
        rw [norm_mul, norm_pow]
        have : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_natCast]; push_cast; ring
      rw [h2]; nlinarith [ih]
    have hnum : 0 ≤ ((tb a k : ℝ) + (k + 1)) * ‖x‖ ^ 2 := by
      have := tb_nonneg ha k
      have h3 : (0 : ℝ) ≤ (tb a k : ℝ) := by exact_mod_cast this
      positivity
    have hnorm : 0 < ‖1 + x‖ := by linarith
    calc ‖((1 + x) ^ k)⁻¹ - 1 + (k : ℂ) * x + ((k : ℂ) + 1) * x ^ 2‖ / ‖1 + x‖
        ≤ (((tb a k : ℝ) + (k + 1)) * ‖x‖ ^ 2) / ‖1 + x‖ := by gcongr
      _ ≤ (((tb a k : ℝ) + (k + 1)) * ‖x‖ ^ 2) / (1 - (a : ℝ)) := by
          apply div_le_div_of_nonneg_left hnum hpos hlow
      _ = (tb a (k + 1) : ℝ) * ‖x‖ ^ 2 := by
          simp only [tb]; push_cast; ring

end CatalanCore.Uniform.Decay.FarField
