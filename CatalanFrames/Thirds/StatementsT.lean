module

public import CatalanFrames.Thirds.MeasureAt
public import CatalanFrames.Thirds.MinorDecayT

@[expose] public section

/-! # Both thirds targets at exponent `1061/100`

These statements require the thirds-specific numerical certificate and its verified decay data.
-/

open CatalanCore CatalanCore.Rect CatalanFrames.P6

namespace CatalanFrames.Thirds

theorem thirds_exponent_checkT :
    (169697 / 25000 : ℚ) / (77423 / 20000 - thirdsSharpPrice) ≤ 1061 / 100 := by
  norm_num [thirdsSharpPrice]

private theorem adm_windowT (r m : ℕ) (h : ThirdsAdm r m) :
    (((1 / 8 : ℚ)) : ℝ) * r ≤ m ∧
      (m : ℝ) ≤ (((1 / 8 : ℚ)) : ℝ) * r + 9 / 8 := by
  obtain ⟨h1, h2⟩ := h
  have a1 : (r : ℝ) ≤ 8 * m := by exact_mod_cast h1
  have a2 : (8 * m : ℝ) ≤ r + 9 := by exact_mod_cast h2
  push_cast
  constructor <;> linarith

/-- `L(2,χ₋₃) + (2/3) ζ(2)`: irrationality exponent `1061/100`. -/
theorem chi3_plus_zeta2_measure_1061 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1061 / 100 : ℚ) : ℝ) + e)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 -
          1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + Real.pi ^ 2 / 9) - (p : ℝ) / q| := by
  exact chi3_plus_zeta2_measure_of_decay (D := 77423 / 20000)
    (c := 169697 / 25000) (E := 1061 / 100)
    (thirdsAc_minorDecayT (a := 9 / 8) (by norm_num) 1 adm_windowT)
    (by norm_num [thirdsSharpPrice]) (by norm_num)
    (by norm_num [thirdsSharpPrice]) thirds_exponent_checkT

/-- `L(2,χ₋₃) - (2/3) ζ(2)`: irrationality exponent `1061/100`. -/
theorem chi3_minus_zeta2_measure_1061 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1061 / 100 : ℚ) : ℝ) + e)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 -
          1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - Real.pi ^ 2 / 9) - (p : ℝ) / q| := by
  exact chi3_minus_zeta2_measure_of_decay (D := 77423 / 20000)
    (c := 169697 / 25000) (E := 1061 / 100)
    (thirdsBc_minorDecayT (a := 9 / 8) (by norm_num) 1 adm_windowT)
    (by norm_num [thirdsSharpPrice]) (by norm_num)
    (by norm_num [thirdsSharpPrice]) thirds_exponent_checkT

end CatalanFrames.Thirds

#print axioms CatalanFrames.Thirds.chi3_plus_zeta2_measure_1061
#print axioms CatalanFrames.Thirds.chi3_minus_zeta2_measure_1061
