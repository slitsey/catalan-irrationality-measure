module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Real

public section

/-!
The strongest hybrid measure statements, with constants written as series:
`G - 5π²/48` and `G + 5π²/48` have exponent 32.44; `L(2, χ₋₃)` has exponent 14.21;
`L(2, χ₋₃) + π²/9` and `L(2, χ₋₃) - π²/9` have exponent 10.61;
the four numbers `ψ'(a/5) - π²/6` (a = 1, 2, 3, 4) have exponent 31.95.
For every positive error in the exponent, the bound holds at all sufficiently
large coprime denominators.
-/

namespace CatalanHybridChallenge

theorem lam_hybrid_measure_3244 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((811 / 25 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| := by
  sorry

theorem mir_hybrid_measure_3244 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((811 / 25 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| := by
  sorry

theorem chi3_hybrid_measure_1421 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1421/100 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - (p : ℝ) / q| := by
  sorry

theorem chi3_plus_pi2_hybrid_measure_1061 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1061 / 100 : ℚ) : ℝ) + e)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          + Real.pi ^ 2 / 9) - (p : ℝ) / q| := by
  sorry

theorem chi3_minus_pi2_hybrid_measure_1061 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1061 / 100 : ℚ) : ℝ) + e)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - Real.pi ^ 2 / 9) - (p : ℝ) / q| := by
  sorry

theorem fifths1_hybrid_measure_3195 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((639 / 20 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + (((((1 : ℕ) : ℚ) / 5 : ℚ)) : ℝ)) ^ 2) - Real.pi ^ 2 / 6)
          - (p : ℝ) / q| :=
  by
  sorry

theorem fifths2_hybrid_measure_3195 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((639 / 20 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + (((((2 : ℕ) : ℚ) / 5 : ℚ)) : ℝ)) ^ 2) - Real.pi ^ 2 / 6)
          - (p : ℝ) / q| :=
  by
  sorry

theorem fifths3_hybrid_measure_3195 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((639 / 20 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + (((((3 : ℕ) : ℚ) / 5 : ℚ)) : ℝ)) ^ 2) - Real.pi ^ 2 / 6)
          - (p : ℝ) / q| :=
  by
  sorry

theorem fifths4_hybrid_measure_3195 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((639 / 20 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + (((((4 : ℕ) : ℚ) / 5 : ℚ)) : ℝ)) ^ 2) - Real.pi ^ 2 / 6)
          - (p : ℝ) / q| :=
  by
  sorry

end CatalanHybridChallenge
