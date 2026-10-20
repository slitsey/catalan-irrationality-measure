module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Real

public section

/-!
# Irrationality measures for `G ∓ 5π²/48` and `L(2, χ₋₃)` (hybrid frames)

Let `G = ∑_{j ≥ 0} (-1)^j / (2j + 1)^2` be Catalan's constant and
`L(2, χ₋₃) = ∑_{k ≥ 0} (1/(3k+1)² - 1/(3k+2)²)`, both written out as `tsum`s.
Each statement says: for every `e > 0` there is `q₀` such that for all integers `p` and natural
numbers `q ≥ q₀` with `p, q` coprime, `|x - p/q| > q ^ (-(E + e))`.  Hence the irrationality
measure of `x` is at most `E`:

* `x = G - 5π²/48`, `E = 34.74` (earlier 38.35 retained);
* `x = G + 5π²/48`, `E = 34.74` (earlier 38.35 retained);
* `x = L(2, χ₋₃)`, `E = 18.50` (with the earlier 23.82 and 21.16 statements retained).

These supersede the earlier square-frame results (kept under `archive/`).
-/

namespace CatalanHybridChallenge

/-- **`μ(G - 5π²/48) ≤ 38.35`.** -/
theorem lam_hybrid_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((3835 / 100 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| := by
  sorry

/-- **`μ(G + 5π²/48) ≤ 38.35`.** -/
theorem mir_hybrid_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((3835 / 100 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| := by
  sorry

/-- **`μ(L(2, χ₋₃)) ≤ 23.82`.** -/
theorem chi3_hybrid_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((2382 / 100 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - (p : ℝ) / q| := by
  sorry

/-- **`μ(G - 5π²/48) ≤ 34.74`, from the uniform interval profile.** -/
theorem lam_hybrid_measure_3474 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1737 / 50 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| := by
  sorry


/-- **`μ(G + 5π²/48) ≤ 34.74`, from the uniform interval profile.** -/
theorem mir_hybrid_measure_3474 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1737 / 50 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| := by
  sorry


theorem chi3_hybrid_measure_2116 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((2116 / 100 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - (p : ℝ) / q| := by
  sorry

theorem chi3_hybrid_measure_1850 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((37 / 2 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - (p : ℝ) / q| := by
  sorry

end CatalanHybridChallenge
