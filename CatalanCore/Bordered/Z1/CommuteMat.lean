module

public import CatalanCore.Bordered.Z1.Commute

/-!
# Z1.2: matrix-level `[T, X′] = 0` over `ℚ`, then over `ℚ[X]`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered.Z1

/-- (1b): `diag(ρ) L̃` is symmetric. -/
theorem rhoLtil_symm (s m : ℕ) (θ : ℚ) :
    Matrix.diagonal (fun a : Fin (s + m) => rho s m θ a) * Ltil s m θ =
      (Ltil s m θ)ᵀ * Matrix.diagonal (fun a : Fin (s + m) => rho s m θ a) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply]
  simp only [Ltil, tri3_apply]
  by_cases h1 : (b : ℕ) = a
  · have : b = a := Fin.ext h1
    subst this; ring
  by_cases h2 : (b : ℕ) = a + 1
  · have key := rho_ratio s m a θ (by have := b.2; omega)
    have h3 : ¬ ((a : ℕ) = b + 1) := by omega
    simp only [h1, h2, h3, if_false, if_true, h2, zero_add, add_zero]
    rw [h2]
    linear_combination key
  by_cases h3 : (a : ℕ) = b + 1
  · have key := rho_ratio s m b θ (by have := a.2; omega)
    simp only [h1, h2, h3, if_false, if_true, zero_add, add_zero]
    rw [h3]
    linear_combination (-1 : ℚ) * key
  · simp [h1, h2, h3]

theorem Amat_Xmat (s m : ℕ) (θ : ℚ) (hθ : 0 < θ) :
    Amat s m θ * Xmat s m θ = (Xmat s m θ)ᵀ * Amat s m θ := by
  have h1 := Lag_mul_Xmat s m θ hθ
  have h2 := rhoLtil_symm s m θ
  set D := Matrix.diagonal (fun a : Fin (s + m) => rho s m θ a) with hD
  calc Amat s m θ * Xmat s m θ
      = (Lag s m θ)ᵀ * (D * (Lag s m θ * Xmat s m θ)) := by
        simp only [Amat, Matrix.mul_assoc]
    _ = (Lag s m θ)ᵀ * ((D * Ltil s m θ) * Lag s m θ) := by
        rw [h1, Matrix.mul_assoc]
    _ = (Lag s m θ)ᵀ * (((Ltil s m θ)ᵀ * D) * Lag s m θ) := by rw [h2]
    _ = (Ltil s m θ * Lag s m θ)ᵀ * (D * Lag s m θ) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (Lag s m θ * Xmat s m θ)ᵀ * (D * Lag s m θ) := by rw [h1]
    _ = (Xmat s m θ)ᵀ * Amat s m θ := by
        simp only [Amat, Matrix.transpose_mul, Matrix.mul_assoc]

theorem Lam2_Xp (s m : ℕ) (θ : ℚ) (hθ : 0 < θ) :
    Matrix.diagonal (fun k : Fin s => Lam2 s m θ k) * Xp s m θ =
      Xmat s m θ * Matrix.diagonal (fun k : Fin s => Lam2 s m θ k) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Xp, Xmat, tri3_apply]
  by_cases h1 : (j : ℕ) = i
  · have : j = i := Fin.ext h1
    subst this; simp [mul_comm]
  by_cases h2 : (j : ℕ) = i + 1
  · have h3 : ¬ ((i : ℕ) = j + 1) := by omega
    simp only [h1, h2, h3, if_false, if_true, zero_add, add_zero]
    rw [h2]
    exact E1a s m i θ hθ (by have := j.2; omega)
  by_cases h3 : (i : ℕ) = j + 1
  · simp only [h1, h2, h3, if_false, if_true, zero_add, add_zero]
    rw [h3]
    exact E1b s m j θ hθ (by have := i.2; omega)
  · simp [h1, h2, h3]

theorem Xp_Lam1 (s m : ℕ) (θ : ℚ) (hθ : 0 < θ) :
    Xp s m θ * Matrix.diagonal (fun k : Fin s => Lam1 s m θ k) =
      Matrix.diagonal (fun k : Fin s => Lam1 s m θ k) * (Xmat s m θ)ᵀ := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply]
  simp only [Xp, Xmat, tri3_apply]
  by_cases h1 : (j : ℕ) = i
  · have : j = i := Fin.ext h1
    subst this; simp [mul_comm]
  by_cases h2 : (j : ℕ) = i + 1
  · have h3 : ¬ ((i : ℕ) = j + 1) := by omega
    have n1 : ¬ ((i : ℕ) = j) := by omega
    simp only [h1, h2, h3, n1, if_false, if_true, zero_add, add_zero]
    rw [h2]
    exact E2a s m i θ hθ (by have := j.2; omega)
  by_cases h3 : (i : ℕ) = j + 1
  · have n1 : ¬ ((i : ℕ) = j) := by omega
    have n2 : ¬ ((j : ℕ) = i + 1) := by omega
    simp only [h1, h2, h3, n1, n2, if_false, if_true, zero_add, add_zero]
    rw [h3]
    exact E2b s m j θ hθ (by have := i.2; omega)
  · have n1 : ¬ ((i : ℕ) = j) := fun h => h1 h.symm
    simp [h1, h2, h3, n1]

/-- **[T, X′] = 0** over `ℚ` at `θ > 0`. -/
theorem Tmat_commute_Xp_rat (s m : ℕ) (θ : ℚ) (hθ : 0 < θ) :
    Tmat s m θ * Xp s m θ = Xp s m θ * Tmat s m θ := by
  have hA := Amat_Xmat s m θ hθ
  have h2 := Lam2_Xp s m θ hθ
  have h1 := Xp_Lam1 s m θ hθ
  set L1 := Matrix.diagonal (fun k : Fin s => Lam1 s m θ k) with hL1
  set L2 := Matrix.diagonal (fun k : Fin s => Lam2 s m θ k) with hL2
  calc Tmat s m θ * Xp s m θ = L1 * Amat s m θ * (L2 * Xp s m θ) := by
        simp only [Tmat, ← hL1, ← hL2, Matrix.mul_assoc]
    _ = L1 * (Amat s m θ * Xmat s m θ) * L2 := by rw [h2]; simp only [Matrix.mul_assoc]
    _ = L1 * ((Xmat s m θ)ᵀ * Amat s m θ) * L2 := by rw [hA]
    _ = (Xp s m θ * L1) * Amat s m θ * L2 := by rw [h1]; simp only [Matrix.mul_assoc]
    _ = Xp s m θ * Tmat s m θ := by
        simp only [Tmat, ← hL1, ← hL2, Matrix.mul_assoc]

end CatalanCore.Bordered.Z1
