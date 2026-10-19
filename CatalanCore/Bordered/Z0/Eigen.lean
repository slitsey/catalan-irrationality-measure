module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Z0.4: lifting a simple spectrum to an eigenbasis over `L⟦X⟧`

If `Y` is a matrix over `L⟦X⟧` (`L` a field) whose constant term is diagonal with pairwise distinct
entries, then `Y` has a full eigenbasis `Y P = P diag η` with `P` invertible, `P(0)` diagonal.
The proof uses Mathlib's `HenselianRing` instance for `L⟦X⟧` (from `IsAdicComplete`), and
eigenvectors are columns of adjugates.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered

open PowerSeries

variable {L : Type*} [Field L] {n : ℕ}

/-- Constant coefficient commutes with polynomial evaluation at a constant. -/
lemma constantCoeff_eval_C (f : Polynomial L⟦X⟧) (x : L) :
    constantCoeff (f.eval (C x)) = (f.map constantCoeff).eval x := by
  rw [Polynomial.eval_map, Polynomial.eval, Polynomial.hom_eval₂]
  simp

/-- **Lemma A (eigenbasis over `L⟦X⟧`).** -/
theorem exists_eigenbasis (Y : Matrix (Fin n) (Fin n) L⟦X⟧) (η₀ : Fin n → L)
    (hη₀ : Function.Injective η₀) (hY : Y.map constantCoeff = diagonal η₀) :
    ∃ (P : Matrix (Fin n) (Fin n) L⟦X⟧) (η : Fin n → L⟦X⟧),
      IsUnit P.det ∧ Matrix.IsDiag (P.map constantCoeff) ∧ (∀ i, (P.map constantCoeff) i i ≠ 0) ∧
      (∀ i, constantCoeff (η i) = η₀ i) ∧ Y * P = P * diagonal η := by
  classical
  set f := Y.charpoly with hfdef
  have hf : f.map constantCoeff = ∏ j, (Polynomial.X - Polynomial.C (η₀ j)) := by
    rw [hfdef, ← Matrix.charpoly_map, hY, charpoly_diagonal]
  -- derivative of the product at a node
  have hder : ∀ i, (f.map constantCoeff).derivative.eval (η₀ i)
      = ∏ j ∈ univ.erase i, (η₀ i - η₀ j) := by
    intro i
    rw [hf, ← Finset.mul_prod_erase univ _ (mem_univ i), Polynomial.derivative_mul]
    simp [Polynomial.eval_prod]
  have hdne : ∀ i, ∏ j ∈ univ.erase i, (η₀ i - η₀ j) ≠ 0 := by
    intro i
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    exact sub_ne_zero.2 fun h => (Finset.mem_erase.1 hj).1 (hη₀ h).symm
  have hroot : ∀ i, ∃ a : L⟦X⟧, f.IsRoot a ∧ constantCoeff a = η₀ i := by
    intro i
    have h1 : f.eval (C (η₀ i)) ∈ Ideal.span {(X : L⟦X⟧)} := by
      rw [Ideal.mem_span_singleton, X_dvd_iff, constantCoeff_eval_C, hf]
      simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact Finset.prod_eq_zero (mem_univ i) (sub_self _)
    have hne := hdne i
    have h2 : IsUnit (Ideal.Quotient.mk (Ideal.span {(X : L⟦X⟧)})
        (f.derivative.eval (C (η₀ i)))) := by
      apply IsUnit.map
      rw [isUnit_iff_constantCoeff]
      have := constantCoeff_eval_C f.derivative (η₀ i)
      rw [← Polynomial.derivative_map, hder] at this
      rw [this]
      exact isUnit_iff_ne_zero.2 hne
    obtain ⟨a, ha, hai⟩ := HenselianRing.is_henselian (I := Ideal.span {(X : L⟦X⟧)}) f
      (Matrix.charpoly_monic Y) (C (η₀ i)) h1 h2
    refine ⟨a, ha, ?_⟩
    rw [Ideal.mem_span_singleton, X_dvd_iff, map_sub, constantCoeff_C, sub_eq_zero] at hai
    exact hai
  choose a ha hac using hroot
  obtain ⟨S, hS⟩ : ∃ S : Fin n → Matrix (Fin n) (Fin n) L⟦X⟧,
      S = fun i => Matrix.scalar (Fin n) (a i) - Y := ⟨_, rfl⟩
  have hdet : ∀ i, (S i).det = 0 := by
    intro i; rw [hS]; simp only; rw [← Matrix.eval_charpoly]; exact ha i
  let P : Matrix (Fin n) (Fin n) L⟦X⟧ := Matrix.of fun r i => (adjugate (S i)) r i
  have hYP : Y * P = P * diagonal a := by
    refine Matrix.ext fun r i => ?_
    have h := congrFun (congrFun (Matrix.mul_adjugate (S i)) r) i
    rw [hdet i, Matrix.mul_apply] at h
    have hSe : ∀ r k, S i r k = (if r = k then a i else 0) - Y r k := by
      intro r k; simp [hS, Matrix.scalar_apply, diagonal_apply]
    simp_rw [hSe, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul] at h
    simp only [Matrix.mul_apply, P, Matrix.of_apply, diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp at h
    rw [mul_comm]; exact (sub_eq_zero.1 h).symm
  have hS0 : ∀ i, (S i).map constantCoeff = diagonal (fun j => η₀ i - η₀ j) := by
    intro i
    refine Matrix.ext fun p q => ?_
    have hy := congrFun (congrFun hY p) q
    simp only [hS, Matrix.map_apply, Matrix.sub_apply, Matrix.scalar_apply, diagonal_apply,
      map_sub] at hy ⊢
    by_cases hpq : p = q
    · subst hpq; simp [hac] at hy ⊢; rw [hy]
    · simp [hpq] at hy ⊢; rw [hy]
  have hP0 : P.map constantCoeff = diagonal (fun i => ∏ j ∈ univ.erase i, (η₀ i - η₀ j)) := by
    refine Matrix.ext fun r i => ?_
    have h1 := RingHom.map_adjugate constantCoeff (S i)
    simp only [RingHom.mapMatrix_apply] at h1
    have h2 := congrFun (congrFun h1 r) i
    rw [hS0, adjugate_diagonal] at h2
    simp only [P, Matrix.map_apply, Matrix.of_apply] at h2 ⊢
    rw [h2]
    simp only [diagonal_apply]
    by_cases hri : r = i
    · subst hri; simp
    · simp [hri]
  refine ⟨P, a, ?_, ?_, ?_, hac, hYP⟩
  · rw [isUnit_iff_constantCoeff]
    have h := RingHom.map_det constantCoeff P
    simp only [RingHom.mapMatrix_apply] at h
    rw [h, hP0, det_diagonal]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hdne i)
  · rw [hP0]; exact isDiag_diagonal _
  · intro i; rw [hP0]; simpa using hdne i

end CatalanCore.Bordered
