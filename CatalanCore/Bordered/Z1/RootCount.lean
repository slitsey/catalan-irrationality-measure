module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Tactic.FieldSimp

/-!
# Z1.5, Lemma 4: a Cauchy sum vanishing at enough nodes has zero coefficients.
-/

@[expose] public section

open Finset Polynomial

namespace CatalanCore.Bordered.Z1

theorem cauchy_root_count (d : ℕ) (v : ℕ → ℝ) (S : Finset ℝ) (hcard : d ≤ S.card)
    (hS : ∀ x ∈ S, ∀ k < d, x + ((k : ℝ) + 1) ≠ 0)
    (h : ∀ x ∈ S, ∑ k ∈ range d, v k / (x + ((k : ℝ) + 1)) = 0) : ∀ k < d, v k = 0 := by
  classical
  intro k0 hk0
  let Q : ℕ → ℝ[X] := fun k => ∏ i ∈ (range d).erase k, (X + C ((i : ℝ) + 1))
  let P : ℝ[X] := ∑ k ∈ range d, C (v k) * Q k
  have hev : ∀ x ∈ S, P.eval x = 0 := by
    intro x hx
    have e : P.eval x = ∑ k ∈ range d, v k * ∏ i ∈ (range d).erase k, (x + ((i : ℝ) + 1)) := by
      simp [P, Q, eval_finset_sum, eval_prod]
    rw [e]
    have hprod : ∀ k ∈ range d, ∏ i ∈ (range d).erase k, (x + ((i : ℝ) + 1)) =
        (∏ i ∈ range d, (x + ((i : ℝ) + 1))) / (x + ((k : ℝ) + 1)) := by
      intro k hk
      rw [eq_div_iff (hS x hx k (mem_range.1 hk)), mul_comm]
      exact Finset.mul_prod_erase (range d) (fun i => x + ((i : ℝ) + 1)) hk
    rw [Finset.sum_congr rfl (fun k hk => by rw [hprod k hk])]
    have : ∑ k ∈ range d, v k * ((∏ i ∈ range d, (x + ((i : ℝ) + 1))) / (x + ((k : ℝ) + 1))) =
        (∏ i ∈ range d, (x + ((i : ℝ) + 1))) * ∑ k ∈ range d, v k / (x + ((k : ℝ) + 1)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, h x hx, mul_zero]
  have hdeg : P.natDegree < S.card := by
    have : P.natDegree ≤ d - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
      refine (natDegree_C_mul_le _ _).trans ?_
      refine (natDegree_prod_le _ _).trans ?_
      simp only [Q, natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
      rw [Finset.card_erase_of_mem hk, Finset.card_range]
    omega
  have hP : P = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P S hev hdeg
  have h0 := congrArg (eval (-((k0 : ℝ) + 1))) hP
  have e : P.eval (-((k0 : ℝ) + 1)) =
      ∑ k ∈ range d, v k * ∏ i ∈ (range d).erase k, (-((k0 : ℝ) + 1) + ((i : ℝ) + 1)) := by
    simp [P, Q, eval_finset_sum, eval_prod]
  rw [e, Finset.sum_eq_single k0] at h0
  · rw [eval_zero] at h0
    have hne : ∏ i ∈ (range d).erase k0, (-((k0 : ℝ) + 1) + ((i : ℝ) + 1)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
      have : i ≠ k0 := (Finset.mem_erase.1 hi).1
      have : (i : ℝ) ≠ k0 := by exact_mod_cast this
      intro h; apply this; linarith
    exact (mul_eq_zero.1 h0).resolve_right hne
  · intro k hk hkk
    have : k0 ∈ (range d).erase k := Finset.mem_erase.2 ⟨fun h => hkk h.symm, mem_range.2 hk0⟩
    rw [Finset.prod_eq_zero this (by ring), mul_zero]
  · intro h; exact absurd (mem_range.2 hk0) h

end CatalanCore.Bordered.Z1
