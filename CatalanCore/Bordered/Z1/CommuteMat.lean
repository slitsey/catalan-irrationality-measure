module

public import CatalanCore.Bordered.Z1.Commute

/-!
# Z1.2: matrix-level `[T, X′] = 0` over `ℚ`, then over `ℚ[X]`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered.Z1

/-- `diag(ρ)`. -/
def Drho (s m : ℕ) (θ : ℚ) : Matrix (Fin (s + m)) (Fin (s + m)) ℚ :=
  Matrix.diagonal (fun a : Fin (s + m) => rho s m θ a)

/-- (1b): `diag(ρ) L̃` is symmetric. -/
theorem rhoLtil_symm (s m : ℕ) (θ : ℚ) :
    Drho s m θ * Ltil s m θ = (Ltil s m θ)ᵀ * Drho s m θ := by
  ext a b
  rw [Drho, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply]
  by_cases h1 : (b : ℕ) = a
  · have : b = a := Fin.ext h1
    subst this; ring
  by_cases h2 : (b : ℕ) = a + 1
  · have key := rho_ratio s m a θ (by have := b.2; omega)
    unfold Ltil; rw [tri3_super _ _ _ h2, tri3_sub _ _ _ h2]
    have hb : (b : ℕ) = a + 1 := h2
    simp only [hb]
    linear_combination key
  by_cases h3 : (a : ℕ) = b + 1
  · have key := rho_ratio s m b θ (by have := a.2; omega)
    unfold Ltil; rw [tri3_sub _ _ _ h3, tri3_super _ _ _ h3]
    simp only [h3]
    linear_combination (-1 : ℚ) * key
  · unfold Ltil; rw [tri3_zero _ _ _ h1 h2 h3, tri3_zero _ _ _ (fun h => h1 h.symm) h3 h2]
    ring

theorem Amat_Xmat (s m : ℕ) (θ : ℚ) (hθ : 0 < θ) :
    Amat s m θ * Xmat s m θ = (Xmat s m θ)ᵀ * Amat s m θ := by
  have h1 := Lag_mul_Xmat s m θ hθ
  have h2 := rhoLtil_symm s m θ
  have hA : Amat s m θ = (Lag s m θ)ᵀ * (Drho s m θ * Lag s m θ) := by
    simp only [Amat, Drho, Matrix.mul_assoc]
  calc Amat s m θ * Xmat s m θ
      = (Lag s m θ)ᵀ * (Drho s m θ * (Lag s m θ * Xmat s m θ)) := by
        rw [hA]; simp only [Matrix.mul_assoc]
    _ = (Lag s m θ)ᵀ * ((Drho s m θ * Ltil s m θ) * Lag s m θ) := by
        rw [h1, Matrix.mul_assoc]
    _ = (Lag s m θ)ᵀ * (((Ltil s m θ)ᵀ * Drho s m θ) * Lag s m θ) := by rw [h2]
    _ = (Ltil s m θ * Lag s m θ)ᵀ * (Drho s m θ * Lag s m θ) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (Lag s m θ * Xmat s m θ)ᵀ * (Drho s m θ * Lag s m θ) := by rw [h1]
    _ = (Xmat s m θ)ᵀ * Amat s m θ := by
        rw [hA]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem Lam2_Xp (s m : ℕ) (θ : ℚ) (hθ : 0 < θ) :
    Matrix.diagonal (fun k : Fin s => Lam2 s m θ k) * Xp s m θ =
      Xmat s m θ * Matrix.diagonal (fun k : Fin s => Lam2 s m θ k) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Xp, Xmat]
  by_cases h1 : (j : ℕ) = i
  · have : j = i := Fin.ext h1
    subst this; rw [tri3_diag, tri3_diag]; ring
  by_cases h2 : (j : ℕ) = i + 1
  · rw [tri3_super _ _ _ h2, tri3_super _ _ _ h2, h2]
    exact E1a s m i θ hθ (by have := j.2; omega)
  by_cases h3 : (i : ℕ) = j + 1
  · rw [tri3_sub _ _ _ h3, tri3_sub _ _ _ h3, h3]
    exact E1b s m j θ hθ (by have := i.2; omega)
  · rw [tri3_zero _ _ _ h1 h2 h3, tri3_zero _ _ _ h1 h2 h3]; ring

theorem Xp_Lam1 (s m : ℕ) (θ : ℚ) (hθ : 0 < θ) :
    Xp s m θ * Matrix.diagonal (fun k : Fin s => Lam1 s m θ k) =
      Matrix.diagonal (fun k : Fin s => Lam1 s m θ k) * (Xmat s m θ)ᵀ := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply, Xp, Xmat]
  by_cases h1 : (j : ℕ) = i
  · have : j = i := Fin.ext h1
    subst this; rw [tri3_diag, tri3_diag]; ring
  by_cases h2 : (j : ℕ) = i + 1
  · rw [tri3_super _ _ _ h2, tri3_sub _ _ _ h2, h2]
    exact E2a s m i θ hθ (by have := j.2; omega)
  by_cases h3 : (i : ℕ) = j + 1
  · rw [tri3_sub _ _ _ h3, tri3_super _ _ _ h3, h3]
    exact E2b s m j θ hθ (by have := i.2; omega)
  · rw [tri3_zero _ _ _ h1 h2 h3, tri3_zero _ _ _ (fun h => h1 h.symm) h3 h2]; ring

/-- **[T, X′] = 0** over `ℚ` at `θ > 0`. -/
theorem Tmat_commute_Xp_rat (s m : ℕ) (θ : ℚ) (hθ : 0 < θ) :
    Tmat s m θ * Xp s m θ = Xp s m θ * Tmat s m θ := by
  have hA := Amat_Xmat s m θ hθ
  have h2 := Lam2_Xp s m θ hθ
  have h1 := Xp_Lam1 s m θ hθ
  calc Tmat s m θ * Xp s m θ
      = Matrix.diagonal (fun k : Fin s => Lam1 s m θ k) * Amat s m θ *
        (Matrix.diagonal (fun k : Fin s => Lam2 s m θ k) * Xp s m θ) := by
        simp only [Tmat, Matrix.mul_assoc]
    _ = Matrix.diagonal (fun k : Fin s => Lam1 s m θ k) * (Amat s m θ * Xmat s m θ) *
        Matrix.diagonal (fun k : Fin s => Lam2 s m θ k) := by
        rw [h2]; simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal (fun k : Fin s => Lam1 s m θ k) * ((Xmat s m θ)ᵀ * Amat s m θ) *
        Matrix.diagonal (fun k : Fin s => Lam2 s m θ k) := by rw [hA]
    _ = (Xp s m θ * Matrix.diagonal (fun k : Fin s => Lam1 s m θ k)) * Amat s m θ *
        Matrix.diagonal (fun k : Fin s => Lam2 s m θ k) := by
        rw [h1]; simp only [Matrix.mul_assoc]
    _ = Xp s m θ * Tmat s m θ := by simp only [Tmat, Matrix.mul_assoc]

end CatalanCore.Bordered.Z1
