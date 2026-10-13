module

public import CatalanMeasure.SparseMain

public section

/-!
# Proofs of the advertised statements

The statements are those of `Challenge.lean`; the proofs are the theorems
`OAI.InternalCatalan.catalan_irrationalityMeasure_2742` and
`OAI.InternalCatalan.catalan_irrationalityMeasure_7675` of `CatalanMeasure/SparseMain.lean`, where
Catalan's constant is OpenAI's `OAI.InternalCatalan.catalan`, defined as the same series.
-/

namespace CatalanIrrationalityMeasure

theorem catalan_irrationalityMeasure_2742 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(2742 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  OAI.InternalCatalan.catalan_irrationalityMeasure_2742

theorem catalan_irrationalityMeasure_7675 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(7675 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  OAI.InternalCatalan.catalan_irrationalityMeasure_7675

end CatalanIrrationalityMeasure
