module

public import CatalanCore.Star.Leonard.DeltaCB
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Prop hDelta, step (3): Hankel determinant in the monic bases `φ_p, ψ_q`

For monic polynomials `φ_p`, `ψ_q` of degree `p`, `q` (`p, q < m`):
`det[∑_a ρ(a) φ_p(a) ψ_q(a)] = det[∑_a ρ(a) a^{p+q}]` (unitriangular change of basis, both sides).
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- coefficient matrix of monic polynomials `φ_p` (`p < m`): `L p k = coeff k` -/
noncomputable def coefMat {m : ℕ} (φ : Fin m → F[X]) : Matrix (Fin m) (Fin m) F :=
  Matrix.of fun p k => (φ p).coeff k

lemma coefMat_det {m : ℕ} (φ : Fin m → F[X]) (hmon : ∀ p, (φ p).Monic)
    (hdeg : ∀ p, (φ p).natDegree = p) : (coefMat φ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [coefMat, Finset.prod_eq_one, fun p => by simpa [hdeg p] using (hmon p).coeff_natDegree]
  · intro p k hpk
    simp only [coefMat, Matrix.of_apply]
    exact coeff_eq_zero_of_natDegree_lt (by rw [hdeg p]; exact hpk)

lemma eval_eq_coefMat {m : ℕ} (φ : Fin m → F[X]) (hdeg : ∀ p, (φ p).natDegree = p) (p : Fin m) (x : F) :
    (φ p).eval x = ∑ k : Fin m, coefMat φ p k * x ^ (k : ℕ) := by
  rw [Polynomial.eval_eq_sum_range' (n := m) (by rw [hdeg p]; exact p.2)]
  rw [← Fin.sum_univ_eq_sum_range (fun k => (φ p).coeff k * x ^ k) m]
  rfl

/-- **Step (3a).** -/
theorem hankel_basis_change {K m : ℕ} (ρ : Fin K → F) (φ ψ : Fin m → F[X])
    (hφm : ∀ p, (φ p).Monic) (hφd : ∀ p, (φ p).natDegree = p)
    (hψm : ∀ p, (ψ p).Monic) (hψd : ∀ p, (ψ p).natDegree = p) :
    (Matrix.of fun (p q : Fin m) => ∑ a : Fin K, ρ a * (φ p).eval ((a : ℕ) : F) *
        (ψ q).eval ((a : ℕ) : F)).det =
      ((Vm K m : Matrix (Fin K) (Fin m) F)ᵀ * Matrix.diagonal ρ * Vm K m).det := by
  have hV : ∀ (χ : Fin m → F[X]), (∀ p, (χ p).natDegree = p) →
      (Matrix.of fun (a : Fin K) (p : Fin m) => (χ p).eval ((a : ℕ) : F)) =
        (Vm K m : Matrix (Fin K) (Fin m) F) * (coefMat χ)ᵀ := by
    intro χ hχ
    ext a p
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Vm]
    rw [eval_eq_coefMat χ hχ p]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have h : (Matrix.of fun (p q : Fin m) => ∑ a : Fin K, ρ a * (φ p).eval ((a : ℕ) : F) *
        (ψ q).eval ((a : ℕ) : F)) =
      coefMat φ * ((Vm K m : Matrix (Fin K) (Fin m) F)ᵀ * Matrix.diagonal ρ * Vm K m) *
        (coefMat ψ)ᵀ := by
    have h1 : (Matrix.of fun (p q : Fin m) => ∑ a : Fin K, ρ a * (φ p).eval ((a : ℕ) : F) *
        (ψ q).eval ((a : ℕ) : F)) =
        (Matrix.of fun (a : Fin K) (p : Fin m) => (φ p).eval ((a : ℕ) : F))ᵀ * Matrix.diagonal ρ *
          (Matrix.of fun (a : Fin K) (p : Fin m) => (ψ p).eval ((a : ℕ) : F)) := by
      ext p q
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.of_apply, Matrix.transpose_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [h1, hV φ hφd, hV ψ hψd, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, coefMat_det φ hφm hφd,
    coefMat_det ψ hψm hψd]
  ring

end CatalanCore.Star.Leonard
