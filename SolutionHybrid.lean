module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Real

import CatalanFrames.LambdaHybrid.FinalS
import CatalanFrames.LambdaMirrorHybrid.FinalS
import CatalanCore.Measure.Scaling
import CatalanFrames.P6Hybrid.QuarterDecay

public section

/-!
Proofs of the strongest statements in `ChallengeHybrid.lean`.
The slope-5/2 decay certificate with the merged non-clean content profile gives both 32.44
bounds (`lam_hybrid_measure_3244`, `mir_hybrid_measure_3244`); the 34.74 statements are kept as
corollaries by monotonicity in the exponent; periodic content and
characteristic-zero selection with a quarter border give 14.35. `MeasureLBAt` unfolds to the displayed statements.
-/

namespace CatalanHybridChallenge

open CatalanCore

theorem lam_hybrid_measure_3244 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((811 / 25 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| :=
  CatalanFrames.LambdaHybrid.lam_hyb_measure_final2

theorem lam_hybrid_measure_3474 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1737 / 50 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| := by
  have h := Measure.MeasureLBAt.mono (E' := ((1737 / 50 : ℚ) : ℝ)) (by norm_num)
    CatalanFrames.LambdaHybrid.lam_hyb_measure_final2
  exact h

theorem mir_hybrid_measure_3244 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((811 / 25 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| :=
  CatalanFrames.LambdaMirrorHybrid.mir_hyb_measure_final2

theorem mir_hybrid_measure_3474 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1737 / 50 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| := by
  have h := Measure.MeasureLBAt.mono (E' := ((1737 / 50 : ℚ) : ℝ)) (by norm_num)
    CatalanFrames.LambdaMirrorHybrid.mir_hyb_measure_final2
  exact h

theorem chi3_hybrid_measure_1435 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((287/20 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - (p : ℝ) / q| :=
  CatalanFrames.P6Hybrid.Quarter.chi3_measure

#print axioms lam_hybrid_measure_3244
#print axioms mir_hybrid_measure_3244
#print axioms lam_hybrid_measure_3474
#print axioms mir_hybrid_measure_3474
#print axioms chi3_hybrid_measure_1435

end CatalanHybridChallenge
