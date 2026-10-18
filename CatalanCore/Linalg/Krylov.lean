module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Krylov matrices and the cross-ratio lemma (L1)

`krylov A v = [v, A v, …, A^{n-1} v]` and `kdet A v` is its determinant (`u(A, v)` in the
algebraic proof of Theorem A).  If `T` has a cyclic vector `v₀` (`kdet T v₀ ≠ 0`) and `N`
commutes with `T`, then `kdet N v * kdet T v' = kdet N v' * kdet T v` for all `v, v'`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

section RingDefs

variable {F : Type*} [CommRing F] {n : ℕ}

/-- The Krylov matrix `[v, A v, …, A^{n-1} v]`. -/
def krylov (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i k => ((A ^ (k : ℕ)) *ᵥ v) i

/-- The Krylov determinant `u(A, v)`. -/
def kdet (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) : F := (krylov A v).det

lemma krylov_apply (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) (i k : Fin n) :
    krylov A v i k = ((A ^ (k : ℕ)) *ᵥ v) i := rfl

lemma mul_krylov_apply (X A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) (i k : Fin n) :
    (X * krylov A v) i k = (X *ᵥ ((A ^ (k : ℕ)) *ᵥ v)) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, krylov_apply]

section Map

variable {G : Type*} [CommRing G]

lemma krylov_map (f : F →+* G) (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) :
    krylov (A.map f) (f ∘ v) = (krylov A v).map f := by
  ext i k
  simp only [krylov_apply, Matrix.map_apply]
  rw [RingHom.map_mulVec]
  have : (A ^ (k : ℕ)).map f = (A.map f) ^ (k : ℕ) := by
    have := map_pow f.mapMatrix A (k : ℕ)
    simpa using this
  rw [this]

/-- Krylov determinants commute with ring homomorphisms. -/
lemma kdet_map (f : F →+* G) (A : Matrix (Fin n) (Fin n) F) (v : Fin n → F) :
    f (kdet A v) = kdet (A.map f) (f ∘ v) := by
  rw [kdet, kdet, krylov_map, RingHom.map_det]
  rfl

end Map

end RingDefs

variable {F : Type*} [Field F] {n : ℕ}

/-- A matrix commuting with `T` is determined by its value on a cyclic vector. -/
lemma eq_of_commute_of_cyclic {T A B : Matrix (Fin n) (Fin n) F} {v₀ : Fin n → F}
    (hcyc : kdet T v₀ ≠ 0) (hA : Commute A T) (hB : Commute B T)
    (h : A *ᵥ v₀ = B *ᵥ v₀) : A = B := by
  have hunit : IsUnit (krylov T v₀) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hcyc)
  have key : A * krylov T v₀ = B * krylov T v₀ := by
    ext i k
    rw [mul_krylov_apply, mul_krylov_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      (hA.pow_right (k : ℕ)).eq, (hB.pow_right (k : ℕ)).eq, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, h]
  exact hunit.mul_left_inj.1 key

/-- Key step of L1: `krylov N v = krylov T v * M` for a matrix `M` independent of `v`. -/
lemma exists_krylov_factor {T N : Matrix (Fin n) (Fin n) F} {v₀ : Fin n → F}
    (hcyc : kdet T v₀ ≠ 0) (hc : Commute N T) :
    ∃ M : Matrix (Fin n) (Fin n) F, ∀ v, krylov N v = krylov T v * M := by
  have hunit : IsUnit (krylov T v₀) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hcyc)
  refine ⟨(krylov T v₀)⁻¹ * krylov N v₀, fun v => ?_⟩
  set M := (krylov T v₀)⁻¹ * krylov N v₀ with hM
  have hKM : krylov T v₀ * M = krylov N v₀ := by
    rw [hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit),
      Matrix.one_mul]
  -- `N^k = ∑ j, M j k • T^j`
  have hS : ∀ k : Fin n, N ^ (k : ℕ) = ∑ j : Fin n, M j k • T ^ (j : ℕ) := by
    intro k
    refine eq_of_commute_of_cyclic hcyc (hc.pow_left _) ?_ ?_
    · refine Commute.sum_left _ _ _ fun j _ => ?_
      exact ((Commute.refl T).pow_left _).smul_left _
    · ext i
      simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      have := congrFun (congrArg (fun X => X) hKM) i
      have h2 := congrFun this k
      rw [← krylov_apply] at *
      rw [← h2, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [krylov_apply, mul_comm]
  ext i k
  rw [krylov_apply, hS k, Matrix.mul_apply]
  simp [Matrix.sum_mulVec, Matrix.smul_mulVec, krylov_apply, mul_comm]

/-- **L1 (cross-ratio lemma).** -/
theorem kdet_cross_ratio {T N : Matrix (Fin n) (Fin n) F} {v₀ : Fin n → F}
    (hcyc : kdet T v₀ ≠ 0) (hc : Commute N T) (v v' : Fin n → F) :
    kdet N v * kdet T v' = kdet N v' * kdet T v := by
  obtain ⟨M, hM⟩ := exists_krylov_factor hcyc hc
  simp only [kdet, hM, Matrix.det_mul]
  ring

end CatalanCore
