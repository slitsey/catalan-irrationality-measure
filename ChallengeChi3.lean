module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Real

public section

/-!
# The constant `L(2, χ₋₃)` is irrational, with an irrationality measure

Let `χ₋₃` be the nontrivial Dirichlet character modulo `3`.  Then
`L(2, χ₋₃) = ∑_{k ≥ 0} (1/(3k+1)² - 1/(3k+2)²) = 0.7813024…`, written out below as a `tsum`.
The statements say:

* `L(2, χ₋₃)` is irrational;
* for every `e > 0` and all large `q`, every `p` coprime to `q` satisfies
  `|L(2, χ₋₃) - p/q| > q^(-(M + e))` with `M = 224384787/7474000 ≈ 30.022`;
* the round-exponent corollary `|L(2, χ₋₃) - p/q| > q^(-31)` for all large `q`.

Reference: S. Litsey, *Irrationality of L(2, χ₋₃)* (2026), building on OpenAI,
*Catalan's constant is irrational* (2026).
-/

namespace CatalanChi3Challenge

/-- **`L(2, χ₋₃)` is irrational.** -/
theorem chi3_irrational :
    Irrational (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) := by
  sorry

/-- **Irrationality measure of `L(2, χ₋₃)`**, with the explicit exponent
`M = 224384787/7474000 ≈ 30.022`. -/
theorem chi3_irrationalityMeasure {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(((224384787 / 7474000 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - (p : ℝ) / q| := by
  sorry

/-- **Round exponent.** For all sufficiently large `q` and every `p` coprime to `q`,
`q ^ (-31) < |L(2, χ₋₃) - p/q|`. -/
theorem chi3_irrationalityMeasure_31 :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(31 : ℝ)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - (p : ℝ) / q| := by
  sorry

end CatalanChi3Challenge
