module

public import CatalanMeasure.FixedNodeLemma6

public section

/-!
# Proofs of the advertised statements

The statements are those of `Challenge.lean`; the proofs are the theorems
`OAI.InternalCatalan.catalan_irrationalityMeasure_7447` and
`OAI.InternalCatalan.catalan_irrationalityMeasure_21228` of `CatalanMeasure/FixedNodeLemma6.lean`, where
Catalan's constant is OpenAI's `OAI.InternalCatalan.catalan`, defined as the same series.
-/

namespace CatalanIrrationalityMeasure

theorem catalan_irrationalityMeasure_7447 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(7447 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  OAI.InternalCatalan.catalan_irrationalityMeasure_7447

theorem catalan_irrationalityMeasure_21228 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(21228 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  OAI.InternalCatalan.catalan_irrationalityMeasure_21228

end CatalanIrrationalityMeasure
