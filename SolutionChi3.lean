module

public import CatalanFrames.P6.Final

@[expose] public section

/-!
# Proofs of the statements of `ChallengeChi3.lean`

From `CatalanFrames.P6.Final` (`chi3_irrational`, `chi3_irrationalityMeasure`,
`chi3_irrationalityMeasure_37`); `chi3L2` is by definition (`rfl`) the series in the statements.
-/

namespace CatalanChi3Challenge

theorem chi3_irrational :
    Irrational (∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2)) :=
  CatalanFrames.P6.chi3_irrational

theorem chi3_irrationalityMeasure {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(((142297183 / 3910000 : ℚ) : ℝ) + e)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - (p : ℝ) / q| := by
  have := CatalanFrames.P6.chi3_irrationalityMeasure he
  rwa [CatalanFrames.P6.p6Exp_eq] at this

theorem chi3_irrationalityMeasure_37 :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), Nat.Coprime p.natAbs q → q₀ ≤ q →
      (q : ℝ) ^ (-(37 : ℝ)) <
        |(∑' k : ℕ, (1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 - 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2))
          - (p : ℝ) / q| :=
  CatalanFrames.P6.chi3_irrationalityMeasure_37

end CatalanChi3Challenge
