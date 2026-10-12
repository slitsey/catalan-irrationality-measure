module

public import CatalanMeasure.WeightedLemma6

public section

/-!
# Proofs of the advertised statements

The statements are those of `Challenge.lean`; the proofs are the theorems
`OAI.InternalCatalan.catalan_irrationalityMeasure_7891` and
`OAI.InternalCatalan.catalan_irrationalityMeasure_22494` of `CatalanMeasure/WeightedLemma6.lean`, where
Catalan's constant is OpenAI's `OAI.InternalCatalan.catalan`, defined as the same series.
-/

namespace CatalanIrrationalityMeasure

theorem catalan_irrationalityMeasure_7891 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(7891 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  OAI.InternalCatalan.catalan_irrationalityMeasure_7891

theorem catalan_irrationalityMeasure_22494 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(22494 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  OAI.InternalCatalan.catalan_irrationalityMeasure_22494

end CatalanIrrationalityMeasure
