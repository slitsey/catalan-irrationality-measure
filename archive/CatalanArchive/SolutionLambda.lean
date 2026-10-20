module

public import CatalanArchive.CatalanLambda.Final
public import CatalanArchive.CatalanLambda.Mirror.FinalG

@[expose] public section

/-!
# Proofs of the statements of `ChallengeLambda.lean`

All statements follow from the certificate-instantiated theorems of `CatalanLambda.Final`
(`lambda_irrational_final`, `lambda_measure_final`, `lambda_measure_78`), where
`CatalanLambda.Decay.catalanG` is the series `∑' j, (-1)^j / (2j+1)^2` (Catalan's constant, equal
by `rfl` to OpenAI's `OAI.InternalCatalan.catalan`).
-/

namespace CatalanLambdaChallenge

theorem lambda_irrational :
    Irrational ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
      - 5 * Real.pi ^ 2 / 96) :=
  CatalanLambda.lambda_irrational_final

theorem lambda_irrationalityMeasure {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(((31682445459 / 409965000 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
          - 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  have := CatalanLambda.lambda_measure_final he
  rwa [CatalanLambda.lambdaMeasureExp_eq] at this

theorem lambda_irrationalityMeasure_78 :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
          - 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| :=
  CatalanLambda.lambda_measure_78

theorem lambdaMirror_irrational :
    Irrational ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
      + 5 * Real.pi ^ 2 / 96) :=
  CatalanLambda.Mirror.lambda_mirror_irrational_final

theorem lambdaMirror_irrationalityMeasure {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(((31682445459 / 409965000 : ℚ) : ℝ) + e)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
          + 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| := by
  have := CatalanLambda.Mirror.lambda_mirror_measure_final he
  rwa [CatalanLambda.lambdaMeasureExp_eq] at this

theorem lambdaMirror_irrationalityMeasure_78 :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(78 : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) / 2
          + 5 * Real.pi ^ 2 / 96) - (p : ℝ) / q| :=
  CatalanLambda.Mirror.lambda_mirror_measure_78

theorem catalan_add_irrational :
    Irrational ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48) :=
  CatalanLambda.Mirror.catalan_add_irrational

theorem catalan_add_irrationalityMeasure_79 :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(79 : ℝ)) <
        |((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) + 5 * Real.pi ^ 2 / 48)
          - (p : ℝ) / q| :=
  CatalanLambda.Mirror.catalan_add_measure_79

end CatalanLambdaChallenge

