module

public import CatalanCore.Linalg.CauchyBinet
public import CatalanCore.Linalg.Cauchy
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Prop hDelta, steps (1)-(2): Cauchy-Binet reduction (package H6)

For the Cauchy matrices `C_X = [1/(a + x_i)]`, `C_Y = [1/(a + y_j)]` (`a < K`, `x, y : Fin m → F`):

`det (C_Xᵀ C_Y) = V(x) V(y) · ∑_{|P| = m} V(P)² ∏_{a∈P} ρ(a)`, `ρ(a) = 1/∏_j (a+x_j)(a+y_j)`

(`delta_CB`), and the sum equals the Hankel determinant `det (Vᵀ diag(ρ) V)` of the moments of `ρ`
(`delta_hankel`).
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- Cauchy matrix: rows `a < K`, entries `1/(a + t_i)`. -/
def Cm (K : ℕ) {m : ℕ} (t : Fin m → F) : Matrix (Fin K) (Fin m) F :=
  Matrix.of fun a i => 1 / (((a : ℕ) : F) + t i)

/-- The weight `ρ(a) = 1/∏_j (a+x_j)(a+y_j)`. -/
def rho {m : ℕ} (xs ys : Fin m → F) (a : ℕ) : F :=
  (∏ j, (((a : ℕ) : F) + xs j) * (((a : ℕ) : F) + ys j))⁻¹

/-- Vandermonde product `V(v) = ∏_{i<j} (v_j - v_i)`. -/
def Vprod {m : ℕ} (v : Fin m → F) : F := ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (v j - v i)

theorem delta_CB {K m : ℕ} (xs ys : Fin m → F)
    (hx : ∀ (a : Fin K) (i : Fin m), ((a : ℕ) : F) + xs i ≠ 0)
    (hy : ∀ (a : Fin K) (i : Fin m), ((a : ℕ) : F) + ys i ≠ 0) :
    ((Cm K xs)ᵀ * Cm K ys).det =
      Vprod xs * Vprod ys * ∑ P : {P : Finset (Fin K) // P.card = m},
        Vprod (fun i => (((CatalanCore.colsOf P i : Fin K) : ℕ) : F)) ^ 2 *
          ∏ i : Fin m, rho xs ys ((CatalanCore.colsOf P i : Fin K) : ℕ) := by
  rw [CatalanCore.det_mul_eq_sum_subsets, Finset.mul_sum]
  refine Finset.sum_congr rfl fun P _ => ?_
  set x' : Fin m → F := fun i => (((CatalanCore.colsOf P i : Fin K) : ℕ) : F) with hx'
  have hX : (Cm K xs)ᵀ.submatrix id (CatalanCore.colsOf P) =
      (Matrix.of fun i j => 1 / (x' i + xs j))ᵀ := by
    ext i j; simp [Cm, hx']
  have hY : (Cm K ys).submatrix (CatalanCore.colsOf P) id =
      Matrix.of fun i j => 1 / (x' i + ys j) := by
    ext i j; simp [Cm, hx']
  rw [hX, hY, Matrix.det_transpose,
    CatalanCore.cauchy_det x' xs (fun i j => hx _ _),
    CatalanCore.cauchy_det x' ys (fun i j => hy _ _)]
  have hN : ∀ (u v : Fin m → F), ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, ((u j - u i) * (v j - v i)) =
      Vprod u * Vprod v := by
    intro u v
    unfold Vprod
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
  rw [hN, hN]
  unfold rho
  rw [Finset.prod_inv_distrib]
  have hD : ∏ i : Fin m, ∏ j : Fin m, ((x' i + xs j) * (x' i + ys j)) =
      (∏ i : Fin m, ∏ j : Fin m, (x' i + xs j)) * ∏ i : Fin m, ∏ j : Fin m, (x' i + ys j) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
  simp only [hx']
  have hD' : ∏ i : Fin m, ∏ j : Fin m,
      ((((CatalanCore.colsOf P i : Fin K) : ℕ) : F) + xs j) *
        ((((CatalanCore.colsOf P i : Fin K) : ℕ) : F) + ys j) =
      (∏ i : Fin m, ∏ j : Fin m, (x' i + xs j)) * ∏ i : Fin m, ∏ j : Fin m, (x' i + ys j) := hD
  rw [hD']
  ring

/-- The `K × m` Vandermonde matrix of the nodes `a < K`. -/
def Vm (K m : ℕ) : Matrix (Fin K) (Fin m) F :=
  Matrix.of fun a p => (((a : ℕ) : F)) ^ (p : ℕ)

theorem delta_hankel {K m : ℕ} (xs ys : Fin m → F) :
    ∑ P : {P : Finset (Fin K) // P.card = m},
        Vprod (fun i => (((CatalanCore.colsOf P i : Fin K) : ℕ) : F)) ^ 2 *
          ∏ i : Fin m, rho xs ys ((CatalanCore.colsOf P i : Fin K) : ℕ) =
      ((Vm K m : Matrix (Fin K) (Fin m) F)ᵀ *
        Matrix.diagonal (fun a : Fin K => rho xs ys (a : ℕ)) * Vm K m).det := by
  rw [CatalanCore.det_transpose_mul_diagonal_mul]
  refine Finset.sum_congr rfl fun P _ => ?_
  have hV : (Vm K m : Matrix (Fin K) (Fin m) F).submatrix (CatalanCore.colsOf P) id =
      Matrix.vandermonde (fun i => (((CatalanCore.colsOf P i : Fin K) : ℕ) : F)) := by
    ext i j; simp [Vm, Matrix.vandermonde]
  have hp : ∏ p ∈ P.1, rho xs ys (p : ℕ) = ∏ i, rho xs ys ((CatalanCore.colsOf P i : Fin K) : ℕ) := by
    have := Finset.prod_map Finset.univ (CatalanCore.colsOf P).toEmbedding
      (fun p : Fin K => rho xs ys (p : ℕ))
    rw [CatalanCore.colsOf, Finset.map_orderEmbOfFin_univ] at this
    exact this
  rw [hV, hp, Matrix.det_vandermonde]
  unfold Vprod
  ring

/-- **Prop hDelta, steps (1)–(2).**  `Δ = V(x) V(y) · det[∑_a ρ(a) a^{p+q}]_{p,q<m}`. -/
theorem delta_eq_hankel {K m : ℕ} (xs ys : Fin m → F)
    (hx : ∀ (a : Fin K) (i : Fin m), ((a : ℕ) : F) + xs i ≠ 0)
    (hy : ∀ (a : Fin K) (i : Fin m), ((a : ℕ) : F) + ys i ≠ 0) :
    ((Cm K xs)ᵀ * Cm K ys).det = Vprod xs * Vprod ys *
      ((Vm K m : Matrix (Fin K) (Fin m) F)ᵀ *
        Matrix.diagonal (fun a : Fin K => rho xs ys (a : ℕ)) * Vm K m).det := by
  rw [delta_CB xs ys hx hy, delta_hankel]

end CatalanCore.Star.Leonard
