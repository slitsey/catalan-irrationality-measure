module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import CatalanCore.Zeta5.Port.Construction

@[expose] public section

/-! Ported from mo271/Zeta5 (Apache-2.0), commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/Legendre.lean (Moritz Firsching); changes: module conversion; only `padicValNat_finset_prod` and `S_eq_div` are ported (the theorem `vS_eq` is stated through `InnerData` of `Apery/Normalization.lean`, which is the content side's, and is not ported here); imports renamed. -/

/-!
# `S_K` as a quotient of natural numbers (5.3)

`S_eq_div` writes `S_K` as `A / B` with `A, B : ℕ`; combined with Legendre's formula
(`padicValNat_factorial`) this gives the valuation of `S_K` used on the content side.
-/

open Finset

namespace Apery

lemma padicValNat_finset_prod (p : ℕ) [hp : Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValNat.mul (hf a (Finset.mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- `S_K` as a quotient of natural numbers. -/
lemma S_eq_div (n : ℕ) :
    S n = (((40 * n).factorial ^ (2 * (37 * n)) * 4 ^ (37 * n - 1) : ℕ) : ℚ) /
      (((3 * n).factorial ^ (12 * (37 * n)) * ∏ i ∈ Icc 1 (37 * n - 1), (2 * i).factorial ^ 2 : ℕ) : ℚ) := by
  unfold S
  push_cast
  ring

end Apery
