/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/OriginalPartialFractions.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Base.OriginalPulledRepresentation

set_option backward.privateInPublic true

@[expose] public section

/-! The literal quotient/remainder decomposition for every rational numerator,
not just a monomial entry of the original matrix. -/
open Polynomial
open scoped BigOperators
namespace CatalanCore.Li2.Port.Li2
noncomputable section

lemma originalResidue_generic (m : ℕ) (F : ℚ[X]) (j : ℕ) :
    SimplePoles.resP F (negativePoles m) (-(j:ℤ)) = originalResidue m F j := by
  unfold SimplePoles.resP originalResidue negativePoles
  rw [← Finset.image_erase negative_nat_injective, Finset.prod_image]
  · simp only [Int.cast_neg, Int.cast_natCast, neg_sub_neg]
  · intro a _ b _ h
    exact negative_nat_injective h

theorem original_partial_fractions (m : ℕ) (F : ℚ[X]) :
    F = (F /ₘ D m)*D m +
      ∑ j ∈ Finset.Icc 1 m, C (originalResidue m F j)*
        ∏ l ∈ (Finset.Icc 1 m).erase j, (X+C (l:ℚ)) := by
  have h := SimplePoles.partial_fractionsP F (negativePoles m)
  rw [SimplePoles.polyPart, negativePoles_product] at h
  conv_lhs => rw [h]
  congr 1
  unfold negativePoles
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j _
    rw [show SimplePoles.resP F
      ((Finset.Icc 1 m).image (fun j:ℕ => -(j:ℤ))) (-(j:ℤ)) = originalResidue m F j
        from originalResidue_generic m F j]
    rw [← Finset.image_erase negative_nat_injective, Finset.prod_image]
    · simp only [Int.cast_neg, Int.cast_natCast, C_neg, sub_neg_eq_add]
    · intro a _ b _ he
      exact negative_nat_injective he
  · intro a _ b _ he
    exact negative_nat_injective he

end
end CatalanCore.Li2.Port.Li2

end
