module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

import CatalanMeasure.Parametric.U6Main

public section

/-!
Proof of the strongest statement in `Challenge.lean`, using Lemma U6 content
and the existing canonical determinant assembly.
-/

namespace CatalanIrrationalityMeasure

theorem catalan_irrationalityMeasure_740 :
    ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(740 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.Parametric.catalan_irrationalityMeasure_740

end CatalanIrrationalityMeasure
