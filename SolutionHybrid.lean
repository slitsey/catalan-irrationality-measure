module

public import CatalanFrames.LambdaHybrid.AssemblyFinal
public import CatalanFrames.LambdaMirrorHybrid.MirFinalAll
public import CatalanFrames.P6Hybrid.Assembly

@[expose] public section

/-!
# Proofs of the statements of `ChallengeHybrid.lean`

From `CatalanFrames.LambdaHybrid.lam_hyb_measure_final`,
`CatalanFrames.LambdaMirrorHybrid.mir_hyb_measure_final` and
`CatalanFrames.P6Hybrid.chi3_hybrid_measure_wide`; `MeasureLBAt x E` unfolds to the displayed
statement.
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

#print axioms lam_hybrid_measure
#print axioms mir_hybrid_measure
#print axioms chi3_hybrid_measure

end CatalanHybridChallenge
