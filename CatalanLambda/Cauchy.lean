module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanLambda

lemma natCast_ne_natCast {p : ℕ} [Fact p.Prime] {a b : ℕ} (ha : a < p) (hb : b < p) (hab : a ≠ b) :
    (a : ZMod p) ≠ (b : ZMod p) := by
  intro h
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact hab h

lemma natCast_ne_zero' {p : ℕ} [Fact p.Prime] {a : ℕ} (ha : 0 < a) (hb : a < p) :
    (a : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd (Nat.le_of_dvd ha h) (by omega)

/-- The square Cauchy matrix `[1/(a+j+1)]`, `0 ≤ a, j < K`, is nonsingular mod `p` when `2K ≤ p`. -/
theorem cauchy_det_ne (p K : ℕ) [Fact p.Prime] (hK : 2 * K ≤ p) :
    (Matrix.of fun (a j : Fin K) => (1 : ZMod p) / ((a : ℕ) + 1 + (j : ℕ))).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  apply hx0
  rcases Nat.eq_zero_or_pos K with hK0 | hK0
  · subst hK0; exact funext fun i => i.elim0
  have hKp : K < p := by omega
  -- the nonvanishing of `a + i + 1`
  have hne : ∀ a i : Fin K, ((a : ℕ) : ZMod p) + 1 + (i : ℕ) ≠ 0 := by
    intro a i
    have := natCast_ne_zero' (p := p) (a := (a : ℕ) + 1 + (i : ℕ)) (by omega) (by
      have := a.2; have := i.2; omega)
    simpa using this
  set P : (ZMod p)[X] := ∑ j : Fin K, C (x j) *
    ∏ i ∈ univ.erase j, (X + C (((i : ℕ) : ZMod p) + 1)) with hP
  have hdeg : P.natDegree < Fintype.card (Fin K) := by
    rw [Fintype.card_fin]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le (n := K - 1) _ _ ?_) (by omega)
    intro j _
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_prod_le _ _).trans ?_
    calc ∑ i ∈ univ.erase j, (X + C (((i : ℕ) : ZMod p) + 1)).natDegree
        ≤ ∑ i ∈ univ.erase j, 1 := by
          apply Finset.sum_le_sum; intro i _; exact (natDegree_X_add_C _).le
      _ = K - 1 := by simp
  have hP0 : P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero P (f := fun a : Fin K => ((a : ℕ) : ZMod p))
      ?_ ?_ hdeg
    · intro a b hab
      by_contra hne'
      exact natCast_ne_natCast (by have := a.2; omega) (by have := b.2; omega)
        (fun h => hne' (Fin.ext h)) hab
    · intro a
      have h1 := congrFun hx a
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h1
      have h2 : P.eval ((a : ℕ) : ZMod p) =
          (∏ i : Fin K, (((a : ℕ) : ZMod p) + 1 + (i : ℕ))) *
            ∑ j : Fin K, 1 / (((a : ℕ) : ZMod p) + 1 + (j : ℕ)) * x j := by
        rw [hP, eval_finsetSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [eval_mul, eval_C, eval_prod]
        simp only [eval_add, eval_X, eval_C]
        have := Finset.mul_prod_erase (univ : Finset (Fin K))
          (fun i => ((a : ℕ) : ZMod p) + 1 + (i : ℕ)) (Finset.mem_univ j)
        rw [← this]
        field_simp [hne a j]
        ring
      rw [h2, h1, mul_zero]
  funext j
  have h3 := congrArg (Polynomial.eval (-(((j : ℕ) : ZMod p) + 1))) hP0
  rw [hP, eval_finsetSum, eval_zero] at h3
  rw [Finset.sum_eq_single j] at h3
  · rw [eval_mul, eval_C, eval_prod] at h3
    simp only [eval_add, eval_X, eval_C] at h3
    rcases mul_eq_zero.1 h3 with h | h
    · simpa using h
    · exfalso
      rw [Finset.prod_eq_zero_iff] at h
      obtain ⟨i, hi, hzero⟩ := h
      have hij : i ≠ j := (Finset.mem_erase.1 hi).1
      have : ((i : ℕ) : ZMod p) = ((j : ℕ) : ZMod p) := by linear_combination hzero
      exact natCast_ne_natCast (by have := i.2; omega) (by have := j.2; omega)
        (fun h => hij (Fin.ext h)) this
  · intro j' _ hj'
    rw [eval_mul, eval_C, eval_prod]
    simp only [eval_add, eval_X, eval_C]
    rw [Finset.prod_eq_zero (i := j) (Finset.mem_erase.2 ⟨Ne.symm hj', mem_univ j⟩) (by ring)]
    simp
  · simp

end CatalanLambda
