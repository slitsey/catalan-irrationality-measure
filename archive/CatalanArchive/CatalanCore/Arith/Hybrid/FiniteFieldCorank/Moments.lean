module

public import CatalanCore.Arith.Hybrid.FiniteFieldCorank.Interpolation
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

open Polynomial Matrix Finset

namespace CatalanCore.Arith.Hybrid.FiniteFieldCorank

variable {k : Type*} [Field k] [DecidableEq k]

/-- A finite Hankel moment matrix, with no frame-specific support. -/
noncomputable def momentMatrix (s : Finset k) (w : k → k) (n : ℕ) :
    Matrix (Fin n) (Fin n) k := fun i j => ∑ y ∈ s, w y * y ^ (i.val + j.val)

lemma eval_ofFn_eq (n : ℕ) (v : Fin n → k) (y : k) :
    (Polynomial.ofFn n v).eval y = ∑ j : Fin n, v j * y ^ j.val := by
  rw [ofFn_eq_sum_monomial, eval_finsetSum]
  simp

/-- A kernel vector is exactly a polynomial annihilating the first n moments. -/
lemma momentMatrix_mulVec (s : Finset k) (w : k → k) (n : ℕ)
    (v : Fin n → k) (i : Fin n) :
    (momentMatrix s w n *ᵥ v) i =
      ∑ y ∈ s, w y * (Polynomial.ofFn n v).eval y * y ^ i.val := by
  classical
  simp only [Matrix.mulVec, dotProduct, momentMatrix]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [eval_ofFn_eq, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add]
  ring

/-- Evaluation weighted by a fixed finite support, as a polynomial linear map. -/
noncomputable def numeratorLinear (s : Finset k) (w : k → k) : k[X] →ₗ[k] k[X] where
  toFun P := numerator s (fun a => w a * P.eval a)
  map_add' P Q := by
    simp only [numerator, eval_add, mul_add, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [numerator, eval_smul, smul_eq_mul, mul_left_comm, map_mul]
    simp only [mul_assoc, ← Finset.mul_sum, Algebra.smul_def, algebraMap_eq, RingHom.id_apply]

end CatalanCore.Arith.Hybrid.FiniteFieldCorank
