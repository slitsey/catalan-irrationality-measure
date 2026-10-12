module

public import CatalanMeasure.SquareMain

public section

/-!
# Proofs of the advertised statements

The statements are those of `Challenge.lean`; the proofs are the theorems
`OAI.InternalCatalan.catalan_irrationalityMeasure_7181` and
`OAI.InternalCatalan.catalan_irrationalityMeasure_20993` of `CatalanMeasure/SquareMain.lean` and `SeparateLemma6.lean`, where
Catalan's constant is OpenAI's `OAI.InternalCatalan.catalan`, defined as the same series.
-/

namespace CatalanIrrationalityMeasure

theorem catalan_irrationalityMeasure_7181 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(7181 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  OAI.InternalCatalan.catalan_irrationalityMeasure_7181

theorem catalan_irrationalityMeasure_20993 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(20993 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  OAI.InternalCatalan.catalan_irrationalityMeasure_20993

end CatalanIrrationalityMeasure
