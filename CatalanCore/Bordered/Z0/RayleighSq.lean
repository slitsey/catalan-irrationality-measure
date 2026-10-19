module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Data.Matrix.Mul
public import CatalanCore.Bordered.Z0.Small

/-!
# Z0.8: Lemma C (Rayleigh quotient is a square)

For symmetric `A, N` over `L⟦X⟧` and `g` with `A g = σ N g`, if `(A₀ - N₀) g₀ = 0`,
`g₀ᵀ (A₁ - N₁) g₀ = 0` and `g₀ᵀ N₀ g₀ ≠ 0`, then `X² ∣ σ - 1`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered

open PowerSeries

variable {L : Type*} [Field L] {n : ℕ}

/-- The quadratic form of a symmetric matrix with `M₀ g₀ = 0` and `g₀ᵀ M₁ g₀ = 0` is `O(X²)`. -/
lemma X_sq_dvd_quad (M : Matrix (Fin n) (Fin n) L⟦X⟧) (hM : Mᵀ = M) (g : Fin n → L⟦X⟧)
    (h0 : M.map constantCoeff *ᵥ (fun i => constantCoeff (g i)) = 0)
    (h1 : (fun i => constantCoeff (g i)) ⬝ᵥ
      (M.map (coeff 1) *ᵥ (fun i => constantCoeff (g i))) = 0) :
    X ^ 2 ∣ g ⬝ᵥ (M *ᵥ g) := by
  have hM0 : (M.map constantCoeff)ᵀ = M.map constantCoeff := by
    rw [← Matrix.transpose_map, hM]
  rw [X_pow_dvd_iff]
  intro m hm
  interval_cases m
  · have : constantCoeff (g ⬝ᵥ (M *ᵥ g))
        = (fun i => constantCoeff (g i)) ⬝ᵥ (M.map constantCoeff *ᵥ (fun i => constantCoeff (g i))) := by
      simp [dotProduct, Matrix.mulVec, map_sum]
    rw [coeff_zero_eq_constantCoeff_apply, this, h0]; simp
  · have key : coeff 1 (g ⬝ᵥ (M *ᵥ g)) =
        (fun i => coeff 1 (g i)) ⬝ᵥ (M.map constantCoeff *ᵥ (fun i => constantCoeff (g i)))
        + (fun i => constantCoeff (g i)) ⬝ᵥ (M.map (coeff 1) *ᵥ (fun i => constantCoeff (g i)))
        + (fun i => constantCoeff (g i)) ⬝ᵥ (M.map constantCoeff *ᵥ (fun i => coeff 1 (g i))) := by
      simp only [dotProduct, Matrix.mulVec, map_sum, Finset.mul_sum, coeff_one_mul',
        map_mul, Matrix.map_apply, Finset.sum_add_distrib, mul_add]
      rw [add_assoc]
    have h2 : (fun i => constantCoeff (g i)) ⬝ᵥ (M.map constantCoeff *ᵥ (fun i => coeff 1 (g i))) = 0 := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM0, h0]; simp
    rw [key, h0, h1, h2]; simp

/-- **Lemma C (Z0.8).** -/
theorem X_sq_dvd_sub_one (A N : Matrix (Fin n) (Fin n) L⟦X⟧) (hA : Aᵀ = A) (hN : Nᵀ = N)
    (g : Fin n → L⟦X⟧) (σ : L⟦X⟧) (heq : A *ᵥ g = σ • (N *ᵥ g))
    (h0 : (A.map constantCoeff - N.map constantCoeff) *ᵥ (fun i => constantCoeff (g i)) = 0)
    (h1 : (fun i => constantCoeff (g i)) ⬝ᵥ
      ((A.map (coeff 1) - N.map (coeff 1)) *ᵥ (fun i => constantCoeff (g i))) = 0)
    (hpos : (fun i => constantCoeff (g i)) ⬝ᵥ
      (N.map constantCoeff *ᵥ (fun i => constantCoeff (g i))) ≠ 0) :
    X ^ 2 ∣ σ - 1 := by
  have hM : (A - N)ᵀ = A - N := by rw [Matrix.transpose_sub, hA, hN]
  have hq := X_sq_dvd_quad (A - N) hM g
    (by
      have : (A - N).map constantCoeff = A.map constantCoeff - N.map constantCoeff := by
        refine Matrix.ext fun i j => ?_; simp
      rw [this]; exact h0)
    (by
      have : (A - N).map (coeff 1) = A.map (coeff 1) - N.map (coeff 1) := by
        refine Matrix.ext fun i j => ?_; simp
      rw [this]; exact h1)
  have hu : IsUnit (g ⬝ᵥ (N *ᵥ g)) := by
    rw [isUnit_iff_constantCoeff]
    have : constantCoeff (g ⬝ᵥ (N *ᵥ g))
        = (fun i => constantCoeff (g i)) ⬝ᵥ (N.map constantCoeff *ᵥ (fun i => constantCoeff (g i))) := by
      simp [dotProduct, Matrix.mulVec, map_sum]
    rw [this]; exact isUnit_iff_ne_zero.2 hpos
  have hid : g ⬝ᵥ ((A - N) *ᵥ g) = (σ - 1) * (g ⬝ᵥ (N *ᵥ g)) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, heq, dotProduct_smul, smul_eq_mul]; ring
  rw [hid] at hq
  exact (hu.dvd_mul_right).1 hq

end CatalanCore.Bordered
