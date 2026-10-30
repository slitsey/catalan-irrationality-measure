import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Real

import CatalanCore.Uniform.Bank.FourthsContent.Bound
import CatalanCore.Uniform.Bank.Chi3.KContent.Bound
import CatalanCore.Uniform.Bank.ThirdsContent.Bound
import CatalanCore.Uniform.Bank.FifthsContent.Bound
import CatalanCore.Uniform.Bank.SeventhsContent.Bound


/-!
Not yet a `module` file: the bank closures are being converted to the module system; until then this file
imports them as an ordinary file.
Proofs of the statements in `ChallengeHybrid.lean`, from the `Bound` theorems of the trigamma-difference
banks (`CatalanCore.Uniform.Bank.*Content.Bound` and `CatalanCore.Uniform.Bank.Chi3.KContent.Bound`).
`MeasureLBAt` unfolds to the displayed statements; for `G ± 5π²/48` the target is rewritten first.
-/

namespace TrigammaDifferences

open CatalanCore

theorem lambda_minus_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((314411 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48) - (p : ℝ) / q| := by
    have h := CatalanCore.Uniform.Bank.FourthsContent.Bound.lambda_measure false
    have e : CatalanCore.Uniform.Bank.Fourths.lambdaTarget false = (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - 5 * Real.pi ^ 2 / 48 := by
      simp [CatalanCore.Uniform.Bank.Fourths.lambdaTarget, sub_eq_add_neg]
    rw [e] at h
    exact h

theorem lambda_plus_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((314411 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48) - (p : ℝ) / q| := by
    have h := CatalanCore.Uniform.Bank.FourthsContent.Bound.lambda_measure true
    have e : CatalanCore.Uniform.Bank.Fourths.lambdaTarget true = (∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48 := by
      simp [CatalanCore.Uniform.Bank.Fourths.lambdaTarget]
    rw [e] at h
    exact h

theorem chi3_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((137046 / 10000 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - (p : ℝ) / q| :=
  CatalanCore.Uniform.Bank.Chi3.KContent.chi3_measure_L2_k

theorem chi3_plus_pi2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((95133 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) + Real.pi ^ 2 / 9) - (p : ℝ) / q| :=
  CatalanCore.Uniform.Bank.ThirdsContent.Bound.thirds_plus_measure

theorem chi3_minus_pi2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((95133 / 10000 : ℚ) : ℝ) + e)) <
        |((∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) - Real.pi ^ 2 / 9) - (p : ℝ) / q| :=
  CatalanCore.Uniform.Bank.ThirdsContent.Bound.thirds_minus_measure

theorem fifths1_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((47823 / 2000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((1 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| :=
  CatalanCore.Uniform.Bank.FifthsContent.Bound.fifths1_measure

theorem fifths2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((47823 / 2000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((2 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| :=
  CatalanCore.Uniform.Bank.FifthsContent.Bound.fifths2_measure

theorem fifths3_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((47823 / 2000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((3 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| :=
  CatalanCore.Uniform.Bank.FifthsContent.Bound.fifths3_measure

theorem fifths4_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((47823 / 2000 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((4 : ℕ) : ℚ) / 5 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| :=
  CatalanCore.Uniform.Bank.FifthsContent.Bound.fifths4_measure

theorem sevenths1_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((2801 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((1 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| :=
  CatalanCore.Uniform.Bank.SeventhsContent.Bound.sevenths_measure ⟨0, by decide⟩

theorem sevenths2_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((2801 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((2 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| :=
  CatalanCore.Uniform.Bank.SeventhsContent.Bound.sevenths_measure ⟨1, by decide⟩

theorem sevenths3_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((2801 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((3 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| :=
  CatalanCore.Uniform.Bank.SeventhsContent.Bound.sevenths_measure ⟨2, by decide⟩

theorem sevenths4_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((2801 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((4 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| :=
  CatalanCore.Uniform.Bank.SeventhsContent.Bound.sevenths_measure ⟨3, by decide⟩

theorem sevenths5_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((2801 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((5 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| :=
  CatalanCore.Uniform.Bank.SeventhsContent.Bound.sevenths_measure ⟨4, by decide⟩

theorem sevenths6_measure :
    ∀ e : ℝ, 0 < e → ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(((2801 : ℚ) : ℝ) + e)) <
        |((∑' n : ℕ, 1 / ((n : ℝ) + ((((((6 : ℕ) : ℚ) / 7 : ℚ)) : ℝ))) ^ 2) - Real.pi ^ 2 / 6) - (p : ℝ) / q| :=
  CatalanCore.Uniform.Bank.SeventhsContent.Bound.sevenths_measure ⟨5, by decide⟩

#print axioms lambda_minus_measure
#print axioms lambda_plus_measure
#print axioms chi3_measure
#print axioms chi3_plus_pi2_measure
#print axioms chi3_minus_pi2_measure
#print axioms fifths1_measure
#print axioms fifths2_measure
#print axioms fifths3_measure
#print axioms fifths4_measure
#print axioms sevenths1_measure
#print axioms sevenths2_measure
#print axioms sevenths3_measure
#print axioms sevenths4_measure
#print axioms sevenths5_measure
#print axioms sevenths6_measure

end TrigammaDifferences
