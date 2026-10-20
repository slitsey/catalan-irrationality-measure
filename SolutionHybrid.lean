module

public import CatalanFrames.LambdaHybrid.AssemblyFinal
public import CatalanFrames.LambdaMirrorHybrid.MirFinalAll
public import CatalanFrames.P6Hybrid.AssemblySquare
public import CatalanFrames.P6Hybrid.AssemblyMinor

@[expose] public section

/-!
# Proofs of the statements of `ChallengeHybrid.lean`

From `CatalanFrames.LambdaHybrid.lam_hyb_measure_final`,
`CatalanFrames.LambdaMirrorHybrid.mir_hyb_measure_final` and
`CatalanFrames.P6Hybrid.chi3_hybrid_measure_wide`; `MeasureLBAt x E` unfolds to the displayed
statement.

The additional theorem `chi3_hybrid_measure_2116` uses the square-divisor
prime rule and the generic valuation-one nonvanishing argument.

`chi3_hybrid_measure_1850` also uses a generic finite-field corank bound and
a family with at most three common low-node deletions.
-/

namespace CatalanHybridChallenge

theorem lam_hybrid_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((3835 / 100 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| :=
  CatalanFrames.LambdaHybrid.lam_hyb_measure_final

theorem mir_hybrid_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((3835 / 100 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| :=
  CatalanFrames.LambdaMirrorHybrid.mir_hyb_measure_final

theorem chi3_hybrid_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((2382 / 100 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - (p : ℝ) / q| :=
  CatalanFrames.P6Hybrid.chi3_hybrid_measure_wide

theorem chi3_hybrid_measure_2116 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((2116 / 100 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - (p : ℝ) / q| :=
  CatalanFrames.P6Hybrid.chi3_hybrid_measure_square

theorem chi3_hybrid_measure_1850 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((37 / 2 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - (p : ℝ) / q| :=
  CatalanFrames.P6Hybrid.chi3_hybrid_measure_minor

#print axioms lam_hybrid_measure
#print axioms mir_hybrid_measure
#print axioms chi3_hybrid_measure
#print axioms chi3_hybrid_measure_2116
#print axioms chi3_hybrid_measure_1850

end CatalanHybridChallenge
