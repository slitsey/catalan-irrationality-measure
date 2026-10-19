module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Z0.12: real Jacobi spectrum

A real matrix `M` that is tridiagonal with nonzero superdiagonal and symmetrisable by a positive
diagonal `D` (`D⁻¹ M D` symmetric) has a full eigenbasis `M P = P diag η` over `ℝ` with `P`
invertible and `η` injective (simple spectrum).
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered

variable {n : ℕ}

/-- An eigenvector of an upper-banded matrix with nonzero superdiagonal vanishing at index `0`
vanishes. -/
lemma eigvec_zero_of_tri (S : Matrix (Fin n) (Fin n) ℝ)
    (hz : ∀ i j : Fin n, i.val + 2 ≤ j.val → S i j = 0)
    (hnz : ∀ i j : Fin n, j.val = i.val + 1 → S i j ≠ 0)
    (lam : ℝ) (v : Fin n → ℝ) (hv : S *ᵥ v = lam • v) (h0 : ∀ i : Fin n, i.val = 0 → v i = 0) :
    v = 0 := by
  have key : ∀ m : ℕ, ∀ i : Fin n, i.val ≤ m → v i = 0 := by
    intro m
    induction m with
    | zero => intro i hi; exact h0 i (by omega)
    | succ m ih =>
      intro i hi
      by_cases him : i.val ≤ m
      · exact ih i him
      have hi' : i.val = m + 1 := by omega
      have hm : m < n := by omega
      have hrow := congrFun hv ⟨m, hm⟩
      have hsum : (S *ᵥ v) ⟨m, hm⟩ = S ⟨m, hm⟩ i * v i := by
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_eq_single i ?_ (by simp)
        intro k _ hk
        by_cases hkm : k.val ≤ m
        · rw [ih k hkm, mul_zero]
        · by_cases hk2 : k.val = m + 1
          · exact absurd (Fin.ext (by omega)) hk
          · rw [hz ⟨m, hm⟩ k (by simp; omega), zero_mul]
      rw [hsum, Pi.smul_apply, ih ⟨m, hm⟩ le_rfl, smul_zero] at hrow
      exact (mul_eq_zero.1 hrow).resolve_left (hnz ⟨m, hm⟩ i hi')
  funext i
  exact key i.val i le_rfl

/-- Orthonormality of the eigenvector columns of a real symmetric matrix. -/
lemma eigvec_orthonormal (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsHermitian) (j k : Fin n) :
    ∑ i, hS.eigenvectorBasis j i * hS.eigenvectorBasis k i = if j = k then 1 else 0 := by
  have h := congrFun (congrFun (Unitary.coe_star_mul_self hS.eigenvectorUnitary) j) k
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, star_trivial,
    Matrix.transpose_apply, Matrix.conjTranspose_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply] at h
  exact h

/-- A real symmetric upper-banded matrix with nonzero superdiagonal has simple spectrum. -/
theorem eigenvalues_injective_of_tri (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.IsHermitian)
    (hz : ∀ i j : Fin n, i.val + 2 ≤ j.val → S i j = 0)
    (hnz : ∀ i j : Fin n, j.val = i.val + 1 → S i j ≠ 0) :
    Function.Injective hS.eigenvalues := by
  intro j k hjk
  by_contra hne
  have hn : 0 < n := Fin.pos j
  set o : Fin n := ⟨0, hn⟩
  set ej : Fin n → ℝ := ⇑(hS.eigenvectorBasis j)
  set ek : Fin n → ℝ := ⇑(hS.eigenvectorBasis k)
  have hj : S *ᵥ ej = hS.eigenvalues j • ej := hS.mulVec_eigenvectorBasis j
  have hk : S *ᵥ ek = hS.eigenvalues j • ek := by rw [hjk]; exact hS.mulVec_eigenvectorBasis k
  have hu : (ek o • ej - ej o • ek) = 0 := by
    refine eigvec_zero_of_tri S hz hnz (hS.eigenvalues j) _ ?_ ?_
    · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hj, hk]
      simp [smul_smul, mul_comm, smul_sub]
    · intro i hi
      have : i = o := Fin.ext hi
      subst this; simp [mul_comm]
  have hjj := eigvec_orthonormal S hS j j
  have hjk' := eigvec_orthonormal S hS j k
  have hkj := eigvec_orthonormal S hS k j
  have hkk := eigvec_orthonormal S hS k k
  simp only [ite_true] at hjj hkk
  simp only [hne, ite_false] at hjk'
  simp only [Ne.symm hne, ite_false] at hkj
  have e1 : ∀ i, ek o * ej i = ej o * ek i := fun i => by
    have := congrFun hu i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    linarith
  have a0 : ek o = 0 := by
    have h : ∑ i, ek o * ej i * ej i = ∑ i, ej o * ek i * ej i :=
      Finset.sum_congr rfl fun i _ => by rw [e1 i]
    have l1 : ∑ i, ek o * ej i * ej i = ek o := by
      simp only [mul_assoc, ← Finset.mul_sum]; rw [hjj, mul_one]
    have l2 : ∑ i, ej o * ek i * ej i = 0 := by
      simp only [mul_assoc, ← Finset.mul_sum]; rw [hkj, mul_zero]
    rw [l1, l2] at h; exact h
  have b0 : ej o = 0 := by
    have h : ∑ i, ek o * ej i * ek i = ∑ i, ej o * ek i * ek i :=
      Finset.sum_congr rfl fun i _ => by rw [e1 i]
    have l1 : ∑ i, ek o * ej i * ek i = 0 := by
      simp only [mul_assoc, ← Finset.mul_sum]; rw [hjk', mul_zero]
    have l2 : ∑ i, ej o * ek i * ek i = ej o := by
      simp only [mul_assoc, ← Finset.mul_sum]; rw [hkk, mul_one]
    rw [l1, l2] at h; exact h.symm
  have hz0 : ej = 0 := eigvec_zero_of_tri S hz hnz _ ej hj
    (fun i hi => by have : i = o := Fin.ext hi; subst this; exact b0)
  have h1 : ∑ i, ej i * ej i = 1 := hjj
  rw [hz0] at h1
  simp at h1

/-- **Z0.12.** Simple real spectrum of a symmetrisable tridiagonal matrix. -/
theorem exists_real_eigenbasis_tri (M : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i) (hsym : ∀ i j, M i j * d j ^ 2 = M j i * d i ^ 2)
    (hupper : ∀ i j : Fin n, i.val + 2 ≤ j.val → M i j = 0)
    (hsup : ∀ i j : Fin n, j.val = i.val + 1 → M i j ≠ 0) :
    ∃ (P : Matrix (Fin n) (Fin n) ℝ) (η : Fin n → ℝ),
      IsUnit P.det ∧ Function.Injective η ∧ M * P = P * diagonal η := by
  set S : Matrix (Fin n) (Fin n) ℝ := diagonal (fun i => (d i)⁻¹) * M * diagonal d with hSdef
  have hSij : ∀ i j, S i j = (d i)⁻¹ * M i j * d j := by
    intro i j
    simp [hSdef, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hdne : ∀ i, d i ≠ 0 := fun i => (hd i).ne'
  have hSH : S.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [star_trivial, hSij]
    have h := hsym i j
    field_simp [hdne i, hdne j]
    linarith
  have hz : ∀ i j : Fin n, i.val + 2 ≤ j.val → S i j = 0 := by
    intro i j h; rw [hSij, hupper i j h]; simp
  have hnz : ∀ i j : Fin n, j.val = i.val + 1 → S i j ≠ 0 := by
    intro i j h; rw [hSij]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero (hdne i)) (hsup i j h)) (hdne j)
  have hinj := eigenvalues_injective_of_tri S hSH hz hnz
  set U : Matrix (Fin n) (Fin n) ℝ := (hSH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  have hSU : S * U = U * diagonal hSH.eigenvalues := by
    refine Matrix.ext fun i j => ?_
    have h := congrFun (hSH.mulVec_eigenvectorBasis j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, hU, Matrix.IsHermitian.eigenvectorUnitary_apply]
    simpa [mul_comm] using h
  have hUu : IsUnit U.det := by
    have h1 := Unitary.coe_star_mul_self hSH.eigenvectorUnitary
    have h2 : (star U) * U = 1 := h1
    have := congrArg Matrix.det h2
    rw [Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact this⟩
  refine ⟨diagonal d * U, hSH.eigenvalues, ?_, hinj, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal]
    exact (isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => hdne i)).mul hUu
  · have hMD : M * diagonal d = diagonal d * S := by
      refine Matrix.ext fun i j => ?_
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hSij]
      field_simp [hdne i]
    rw [← Matrix.mul_assoc, hMD, Matrix.mul_assoc, hSU, Matrix.mul_assoc]

/-- A tridiagonal matrix with positive off-diagonal products is symmetrisable by a positive
diagonal. -/
theorem exists_symmetriser (M : Matrix (Fin n) (Fin n) ℝ)
    (hupper : ∀ i j : Fin n, i.val + 2 ≤ j.val → M i j = 0)
    (hlower : ∀ i j : Fin n, i.val + 2 ≤ j.val → M j i = 0)
    (hprod : ∀ i j : Fin n, j.val = i.val + 1 → 0 < M i j * M j i) :
    ∃ d : Fin n → ℝ, (∀ i, 0 < d i) ∧ ∀ i j, M i j * d j ^ 2 = M j i * d i ^ 2 := by
  let f : ℕ → ℝ := fun i =>
    if h : i + 1 < n then M ⟨i + 1, h⟩ ⟨i, by omega⟩ / M ⟨i, by omega⟩ ⟨i + 1, h⟩ else 1
  have hf : ∀ i, 0 < f i := by
    intro i
    by_cases h : i + 1 < n
    · simp only [f, dif_pos h]
      have hp := hprod ⟨i, by omega⟩ ⟨i + 1, h⟩ rfl
      exact div_pos_iff.2 (mul_pos_iff.1 (by rwa [mul_comm] at hp))
    · simp [f, h]
  let w : ℕ → ℝ := fun j => ∏ i ∈ Finset.range j, f i
  have hw : ∀ j, 0 < w j := fun j => Finset.prod_pos fun i _ => hf i
  have hws : ∀ j, w (j + 1) = w j * f j := fun j => Finset.prod_range_succ _ _
  refine ⟨fun i => Real.sqrt (w i.val), fun i => Real.sqrt_pos.2 (hw _), ?_⟩
  have hsq : ∀ i : Fin n, Real.sqrt (w i.val) ^ 2 = w i.val := fun i =>
    Real.sq_sqrt (hw _).le
  intro i j
  simp only [hsq]
  have key : ∀ i j : Fin n, j.val = i.val + 1 → M i j * w j.val = M j i * w i.val := by
    intro i j hij
    have hu : M i j ≠ 0 := fun h0 => by have := hprod i j hij; rw [h0] at this; simp at this
    have hfi : f i.val = M j i / M i j := by
      have hh : i.val + 1 < n := by omega
      simp only [f, dif_pos hh]
      have e : j = ⟨i.val + 1, hh⟩ := Fin.ext hij
      subst e; rfl
    rw [hij, hws, hfi]
    field_simp
  rcases lt_trichotomy i.val j.val with h | h | h
  · by_cases h1 : j.val = i.val + 1
    · exact key i j h1
    · rw [hupper i j (by omega), hlower i j (by omega)]; simp
  · have : i = j := Fin.ext h
    subst this; rfl
  · by_cases h1 : i.val = j.val + 1
    · exact (key j i h1).symm
    · rw [hupper j i (by omega), hlower j i (by omega)]; simp

/-- **Z0.12 (irreducible block).** A real tridiagonal matrix with positive off-diagonal products
has a real eigenbasis with simple spectrum. -/
theorem exists_real_eigenbasis (M : Matrix (Fin n) (Fin n) ℝ)
    (hupper : ∀ i j : Fin n, i.val + 2 ≤ j.val → M i j = 0)
    (hlower : ∀ i j : Fin n, i.val + 2 ≤ j.val → M j i = 0)
    (hprod : ∀ i j : Fin n, j.val = i.val + 1 → 0 < M i j * M j i) :
    ∃ (P : Matrix (Fin n) (Fin n) ℝ) (η : Fin n → ℝ),
      IsUnit P.det ∧ Function.Injective η ∧ P⁻¹ * M * P = diagonal η := by
  obtain ⟨d, hd, hsym⟩ := exists_symmetriser M hupper hlower hprod
  obtain ⟨P, η, hP, hη, hMP⟩ := exists_real_eigenbasis_tri M d hd hsym hupper
    (fun i j h h0 => by have := hprod i j h; rw [h0] at this; simp at this)
  refine ⟨P, η, hP, hη, ?_⟩
  rw [Matrix.mul_assoc, hMP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]

end CatalanCore.Bordered
