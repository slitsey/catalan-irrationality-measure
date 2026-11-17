/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/PoleWindowReversal.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Base.PoleDissectionWindow

set_option backward.privateInPublic true

@[expose] public section

/-! Identification of the finite sliding window with the original weights
lambda^(-a), using a literal finite reversal. -/
open scoped BigOperators
namespace CatalanCore.Li2.Port.Li2
noncomputable section

lemma poleDissectionWindow_reverse {K : Type*} [Field K] (z : K) (hz : z ≠ 0)
    (p : ℕ) (F : ℕ → K) (j : ℕ) :
    poleDissectionWindow z p F j =
      ∑ a ∈ Finset.range p, z⁻¹^a*F (j+(p-1-a)) := by
  unfold poleDissectionWindow
  rw [← Finset.sum_range_reflect (fun b => z^b*F (j+b)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have he : p-1-a+a = p-1 := by have := Finset.mem_range.mp ha; omega
  have hw : z⁻¹^(p-1)*z^(p-1-a) = z⁻¹^a := by
    rw [← he, pow_add, inv_pow, inv_pow]
    field_simp
    simp only [Nat.add_sub_cancel]
  rw [← mul_assoc, hw]

end
end CatalanCore.Li2.Port.Li2

end
