module

public import CatalanCore.Linalg.Krylov
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Krylov reduction: Lemmas kr1 + kr2 (and Corollary kr)

For a symmetric `N` and `w` with `u(N, w) ≠ 0`, the matrices `N` and `N + w wᵀ` have no common
eigenvalue: for every `z`, `det(z + N) ≠ 0` or `det(z + N + w wᵀ) ≠ 0`.  Elementary proof, over any
field, with no adjugate/rank argument: an eigenvector `y` of `N + w wᵀ` with `wᵀy ≠ 0` and an
eigenvector `v` of `N` with `wᵀv ≠ 0` would give `0 = vᵀ(z+N)y = -(wᵀy)(wᵀv) ≠ 0`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

variable {F : Type*} [Field F] {n : ℕ}

/-- Lemma kr2. -/
lemma kdet_eq_zero_of_eigen (N : Matrix (Fin n) (Fin n) F) (hN : Nᵀ = N) (w : Fin n → F) (z : F)
    (x : Fin n → F) (hx : x ≠ 0) (hAx : (z • (1 : Matrix (Fin n) (Fin n) F) + N) *ᵥ x = 0)
    (hw : w ⬝ᵥ x = 0) : kdet N w = 0 := by
  have hNx : N *ᵥ x = (-z) • x := by
    have : z • x + N *ᵥ x = 0 := by
      simpa [Matrix.add_mulVec, Matrix.smul_mulVec] using hAx
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_right this
  have hpow : ∀ k : ℕ, (N ^ k) *ᵥ x = (-z) ^ k • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hNx, smul_smul, pow_succ]
  have hzero : x ᵥ* krylov N w = 0 := by
    ext k
    have : (x ᵥ* krylov N w) k = x ⬝ᵥ ((N ^ (k : ℕ)) *ᵥ w) := by
      simp [Matrix.vecMul, dotProduct, krylov_apply]
    rw [this, dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_pow, hN, hpow,
      smul_dotProduct, dotProduct_comm, hw]
    simp
  exact (Matrix.exists_vecMul_eq_zero_iff.1 ⟨x, hx, hzero⟩)

/-- **Corollary kr** (Lemmas kr1 + kr2, elementary proof). -/
theorem no_common_root_of_kdet_ne (N : Matrix (Fin n) (Fin n) F) (hN : Nᵀ = N) (w : Fin n → F)
    (hu : kdet N w ≠ 0) (z : F) :
    (z • (1 : Matrix (Fin n) (Fin n) F) + N).det ≠ 0 ∨
      (z • (1 : Matrix (Fin n) (Fin n) F) + (N + Matrix.vecMulVec w w)).det ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hA'⟩ := hcon
  set A : Matrix (Fin n) (Fin n) F := z • (1 : Matrix (Fin n) (Fin n) F) + N with hAdef
  have hAsymm : Aᵀ = A := by
    rw [hAdef, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hN]
  have hrw : z • (1 : Matrix (Fin n) (Fin n) F) + (N + Matrix.vecMulVec w w) =
      A + Matrix.vecMulVec w w := by rw [hAdef, add_assoc]
  rw [hrw] at hA'
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hA'
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hA
  have vecMulVec_mulVec' : ∀ x : Fin n → F, Matrix.vecMulVec w w *ᵥ x = (w ⬝ᵥ x) • w := by
    intro x
    ext i
    simp only [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Matrix.of_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hy' : A *ᵥ y = -((w ⬝ᵥ y) • w) := by
    rw [Matrix.add_mulVec, vecMulVec_mulVec'] at hy
    exact eq_neg_of_add_eq_zero_left hy
  by_cases hc : w ⬝ᵥ y = 0
  · rw [hc, zero_smul, neg_zero] at hy'
    exact hu (kdet_eq_zero_of_eigen N hN w z y hy0 hy' hc)
  by_cases hd : w ⬝ᵥ v = 0
  · exact hu (kdet_eq_zero_of_eigen N hN w z v hv0 hv hd)
  have h1 : v ⬝ᵥ (A *ᵥ y) = 0 := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hAsymm, hv, zero_dotProduct]
  rw [hy', dotProduct_neg, dotProduct_smul, dotProduct_comm v w] at h1
  simp only [smul_eq_mul, neg_eq_zero, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact hc h1
  · exact hd h1

end CatalanCore
