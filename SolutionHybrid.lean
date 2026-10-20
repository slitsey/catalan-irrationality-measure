module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Real

import CatalanFrames.LambdaHybrid.UniformFinal
import CatalanFrames.LambdaMirrorHybrid.UniformFinal
import CatalanFrames.P6Hybrid.QuarterDecay

public section

/-!
Proofs of the three strongest statements in `ChallengeHybrid.lean`.
The shared uniform profile gives both 34.74 bounds; periodic content and
characteristic-zero selection with a quarter border give 15.50. `MeasureLBAt` unfolds to the displayed statements.
-/

namespace CatalanHybridChallenge

theorem lam_hybrid_measure_3474 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1737 / 50 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| :=
  CatalanFrames.LambdaHybrid.lam_hyb_measure_uniform

theorem mir_hybrid_measure_3474 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1737 / 50 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| :=
  CatalanFrames.LambdaMirrorHybrid.mir_hyb_measure_uniform

theorem chi3_hybrid_measure_1550 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((31 / 2 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - (p : ℝ) / q| :=
  CatalanFrames.P6Hybrid.Quarter.chi3_measure

#print axioms lam_hybrid_measure_3474
#print axioms mir_hybrid_measure_3474
#print axioms chi3_hybrid_measure_1550

end CatalanHybridChallenge
