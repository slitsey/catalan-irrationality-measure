/-
Copyright: Tang, Li2 half irrationality formalization.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE in this directory.
Adapted from Li2Unified/Modular/Base/ClassBasisAppend.lean, revision 950ee9d53914e1afb89c8f835a8bca6ccfaa0108.
Changes: module paths and Li2/Li2Unified/Li2Half namespace prefixes; valuation and PNT interfaces re-export existing project theorems.
-/
module
public import CatalanCore.Li2.Port.Unified.Modular.Base.ClassBasis

set_option backward.privateInPublic true

@[expose] public section

/-! Adding a monic polynomial in the next degree preserves independence. -/
open Polynomial
open scoped BigOperators
namespace CatalanCore.Li2.Port.Li2
variable {F : Type*} [Field F] {h : ℕ}

theorem polynomial_family_independent_append (E : Fin h → F[X])
    (hdeg : ∀ a, (E a).natDegree < h)
    (hind : ∀ v : Fin h → F, (∑ a, C (v a) * E a) = 0 → v = 0)
    (G : F[X]) (hG : G.Monic) (hGdeg : G.natDegree = h)
    (v : Fin (h+1) → F)
    (hv : (∑ a, C (v a) * Fin.cases G E a) = 0) : v = 0 := by
  have hGc : G.coeff h = 1 := by
    rw [← hGdeg, coeff_natDegree]
    exact hG
  have hEc (a : Fin h) : (E a).coeff h = 0 := coeff_eq_zero_of_natDegree_lt (hdeg a)
  rw [Fin.sum_univ_succ] at hv
  simp only [Fin.cases_zero, Fin.cases_succ] at hv
  have hc := congrArg (fun P : F[X] => P.coeff h) hv
  simp only [coeff_add, coeff_C_mul, finset_sum_coeff, coeff_zero, hGc, hEc,
    mul_zero, Finset.sum_const_zero, mul_one, add_zero] at hc
  simp only [hc, C_0, zero_mul, zero_add] at hv
  have hrest := hind (fun a => v a.succ) hv
  funext a
  refine Fin.cases ?_ ?_ a
  · exact hc
  · intro i
    exact congrFun hrest i

lemma polynomial_family_append_degree (E : Fin h → F[X])
    (hdeg : ∀ a, (E a).natDegree < h) (G : F[X]) (hGdeg : G.natDegree = h) :
    ∀ a : Fin (h+1), (Fin.cases G E a : F[X]).natDegree < h+1 := by
  intro a
  refine Fin.cases ?_ ?_ a
  · simpa only [Fin.cases_zero, hGdeg] using Nat.lt_succ_self h
  · intro i
    exact (hdeg i).trans (Nat.lt_succ_self h)

end CatalanCore.Li2.Port.Li2

end
