module

public import CatalanCore.Bordered.Hankel.Binomial
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Basis invariance of the Hankel determinant

For a weighted point set `(x ↦ w x, e x)` the Gram determinant in any basis of monic polynomials of
degrees `0, 1, …, k-1` equals the monomial moment Hankel determinant.  This covers translations of
the nodes and the falling-factorial basis used in `Binomial`.
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Bordered.Hankel

/-- Moment Hankel determinant `det [Σ_x w_x e_x^{a+b}]`. -/
noncomputable def momH (s : Finset ℕ) (w e : ℕ → ℚ) (k : ℕ) : ℚ :=
  (Matrix.of fun a b : Fin k => ∑ x ∈ s, w x * e x ^ ((a : ℕ) + b)).det

theorem gram_monic (s : Finset ℕ) (w e : ℕ → ℚ) (p : ℕ → ℚ[X]) (hm : ∀ i, (p i).Monic)
    (hd : ∀ i, (p i).natDegree = i) (k : ℕ) :
    (Matrix.of fun a b : Fin k => ∑ x ∈ s, w x * (p a).eval (e x) * (p b).eval (e x)).det =
      momH s w e k := by
  set A : Matrix (Fin k) (Fin k) ℚ := Matrix.of fun a c => (p a).coeff c with hA
  have hev : ∀ (a : Fin k) (y : ℚ), (p a).eval y = ∑ c : Fin k, A a c * y ^ (c : ℕ) := by
    intro a y
    rw [Polynomial.eval_eq_sum_range' (n := k) (by rw [hd]; exact a.2)]
    simp only [hA, Matrix.of_apply]
    exact (Fin.sum_univ_eq_sum_range (fun c => (p a).coeff c * y ^ c) k).symm
  have hmat : (Matrix.of fun a b : Fin k => ∑ x ∈ s, w x * (p a).eval (e x) * (p b).eval (e x)) =
      A * (Matrix.of fun a b : Fin k => ∑ x ∈ s, w x * e x ^ ((a : ℕ) + b)) * Aᵀ := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hev]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring
  have hdetA : A.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      simp only [hA, Matrix.of_apply]
      have := (hm i).leadingCoeff
      rwa [Polynomial.leadingCoeff, hd] at this
    · intro a b hab
      simp only [hA, Matrix.of_apply]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [hd]; exact Fin.lt_def.1 hab
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetA, one_mul, mul_one]
  rfl

/-- The falling-factorial Gram determinant is the monomial Hankel determinant. -/
theorem hk_eq_momH (N M k : ℕ) :
    hk N M k = momH (range (N + 1)) (Wt N M) (fun x => (x : ℚ)) k := by
  rw [← gram_monic (range (N + 1)) (Wt N M) (fun x => (x : ℚ)) (fun i => descPochhammer ℚ i)
    (fun i => monic_descPochhammer ℚ i) (fun i => descPochhammer_natDegree ℚ i) k]
  rfl

end CatalanCore.Bordered.Hankel
