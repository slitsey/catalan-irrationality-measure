module

public import CatalanMeasure.Lemma6

public section

/-!
# Proofs of the advertised statements

The statements are those of `Challenge.lean`; the proofs are the theorems
`OAI.InternalCatalan.catalan_irrationalityMeasure_82700` and
`OAI.InternalCatalan.catalan_irrationalityMeasure_245200` of `CatalanMeasure/Lemma6.lean`, where
Catalan's constant is OpenAI's `OAI.InternalCatalan.catalan`, defined as the same series.
-/

namespace CatalanIrrationalityMeasure

theorem catalan_irrationalityMeasure_82700 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(82700 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  OAI.InternalCatalan.catalan_irrationalityMeasure_82700

theorem catalan_irrationalityMeasure_245200 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(245200 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  OAI.InternalCatalan.catalan_irrationalityMeasure_245200

end CatalanIrrationalityMeasure
