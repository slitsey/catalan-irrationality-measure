module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Algebra.InfiniteSum.Real

import CatalanFrames.LambdaHybrid.FinalS
import CatalanFrames.LambdaMirrorHybrid.FinalS
import CatalanCore.Measure.Scaling
import CatalanFrames.Thirds.StatementsT
import CatalanFrames.P6Hybrid.ContourResearch.Cert1421
import CatalanFrames.Fifths.Statements

public section

/-!
Proofs of the strongest statements in `ChallengeHybrid.lean`.
The slope-5/2 decay certificate with the merged non-clean content profile gives both 32.44
bounds (`lam_hybrid_measure_3244`, `mir_hybrid_measure_3244`); periodic content and
characteristic-zero selection with a quarter border and a slope-12/5 contour certificate give 14.21;
the thirds frames with their own decay certificate give `L(2, χ₋₃) ± π²/9` with exponent 10.61;
the fifths frames give `ψ'(a/5) - π²/6` (a = 1, ..., 4) with exponent 31.95. `MeasureLBAt` unfolds to the displayed statements.
-/

namespace CatalanHybridChallenge

open CatalanCore

theorem lam_hybrid_measure_3244 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((811 / 25 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| :=
  CatalanFrames.LambdaHybrid.lam_hyb_measure_final2

theorem mir_hybrid_measure_3244 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((811 / 25 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| :=
  CatalanFrames.LambdaMirrorHybrid.mir_hyb_measure_final2

theorem chi3_hybrid_measure_1421 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1421/100 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - (p : ℝ) / q| :=
  CatalanFrames.P6Hybrid.QuarterContour.Cert1421.chi3_measure

theorem chi3_plus_pi2_hybrid_measure_1061 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1061 / 100 : ℚ) : ℝ) + e)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          + Real.pi ^ 2 / 9) - (p : ℝ) / q| :=
  CatalanFrames.Thirds.chi3_plus_zeta2_measure_1061

theorem chi3_minus_pi2_hybrid_measure_1061 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((1061 / 100 : ℚ) : ℝ) + e)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - Real.pi ^ 2 / 9) - (p : ℝ) / q| :=
  CatalanFrames.Thirds.chi3_minus_zeta2_measure_1061

theorem fifths1_hybrid_measure_3195 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((639 / 20 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + (((((1 : ℕ) : ℚ) / 5 : ℚ)) : ℝ)) ^ 2) - Real.pi ^ 2 / 6)
          - (p : ℝ) / q| :=
  CatalanFrames.Fifths.fifths1_measure_3195

theorem fifths2_hybrid_measure_3195 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((639 / 20 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + (((((2 : ℕ) : ℚ) / 5 : ℚ)) : ℝ)) ^ 2) - Real.pi ^ 2 / 6)
          - (p : ℝ) / q| :=
  CatalanFrames.Fifths.fifths2_measure_3195

theorem fifths3_hybrid_measure_3195 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((639 / 20 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + (((((3 : ℕ) : ℚ) / 5 : ℚ)) : ℝ)) ^ 2) - Real.pi ^ 2 / 6)
          - (p : ℝ) / q| :=
  CatalanFrames.Fifths.fifths3_measure_3195

theorem fifths4_hybrid_measure_3195 :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((639 / 20 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + (((((4 : ℕ) : ℚ) / 5 : ℚ)) : ℝ)) ^ 2) - Real.pi ^ 2 / 6)
          - (p : ℝ) / q| :=
  CatalanFrames.Fifths.fifths4_measure_3195

#print axioms lam_hybrid_measure_3244
#print axioms mir_hybrid_measure_3244
#print axioms chi3_hybrid_measure_1421
#print axioms chi3_plus_pi2_hybrid_measure_1061
#print axioms chi3_minus_pi2_hybrid_measure_1061
#print axioms fifths1_hybrid_measure_3195
#print axioms fifths2_hybrid_measure_3195
#print axioms fifths3_hybrid_measure_3195
#print axioms fifths4_hybrid_measure_3195

end CatalanHybridChallenge
