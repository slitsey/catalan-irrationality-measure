module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Real

public section

/-!
# The constant `λ = G/2 - 5π²/96` is irrational, with an irrationality measure

Catalan's constant is `G = ∑_{j ≥ 0} (-1)^j / (2j + 1)^2`; it is written out below as a `tsum`.
Put `λ = G/2 - 5π²/96`, so that `G - 5π²/48 = 2λ`.  The statements say:

* `λ` is irrational;
* for every `e > 0` and all large `q`, every `p` coprime to `q` satisfies
  `|λ - p/q| > q^(-(M + e))` with `M = 31682445459/409965000 ≈ 77.28`;
* the round-exponent corollary `|λ - p/q| > q^(-78)` for all large `q`.

The file also states the same results for the mirror constant `λ' = G/2 + 5π²/96` (so that
`G + 5π²/48 = 2λ'` and `λ + λ' = G`).

Reference: S. Litsey, *The irrationality measure of a Catalan-type constant* (2026), building on
OpenAI, *Catalan's constant is irrational* (2026).
-/

namespace CatalanLambdaChallenge

/-- **`λ = G/2 - 5π²/96` is irrational.** -/
theorem lambda_irrational :
    Irrational ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
      - 5 * Real.pi ^ 2 / 96) := by
  sorry

/-- **Irrationality measure of `λ`**, with the explicit exponent
`M = 31682445459/409965000 ≈ 77.28`. -/
theorem lambda_irrationalityMeasure {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(((31682445459 / 409965000 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
          - 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  sorry

/-- **Round exponent.** For all sufficiently large `q` and every `p` coprime to `q`,
`q ^ (-78) < |λ - p/q|`. -/
theorem lambda_irrationalityMeasure_78 :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
          - 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  sorry

/-! ### The mirror constant `λ' = G/2 + 5π²/96` and `G + 5π²/48 = 2λ'` -/

/-- **`λ' = G/2 + 5π²/96` is irrational.** -/
theorem lambdaMirror_irrational :
    Irrational ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
      + 5 * Real.pi ^ 2 / 96) := by
  sorry

/-- **Irrationality measure of `λ'`**, with the same explicit exponent
`M = 31682445459/409965000 ≈ 77.28` as for `λ`. -/
theorem lambdaMirror_irrationalityMeasure {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(((31682445459 / 409965000 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
          + 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  sorry

/-- **Round exponent for `λ'`.** For all sufficiently large `q` and every `p` coprime to `q`,
`q ^ (-78) < |λ' - p/q|`. -/
theorem lambdaMirror_irrationalityMeasure_78 :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
          + 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  sorry

/-- **`G + 5π²/48` is irrational** (it equals `2λ'`). -/
theorem catalan_add_irrational :
    Irrational ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48) := by
  sorry

/-- **Irrationality measure of `G + 5π²/48`**, round exponent `79`. -/
theorem catalan_add_irrationalityMeasure_79 :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(79 : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| := by
  sorry

end CatalanLambdaChallenge
