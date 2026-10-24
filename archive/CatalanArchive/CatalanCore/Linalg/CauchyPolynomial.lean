module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic

/-!
# Cauchy residue coordinates and their paired moment matrices

All node data are arbitrary field elements. The polynomial factors are data;
constant-specific arithmetic enters only when instantiating them.
-/

@[expose] public section

open Polynomial Finset Matrix

namespace CatalanCore.Linalg.CauchyPolynomial

variable {k : Type*} [Field k] {K m n : ℕ}

noncomputable def denom (low : Fin K → k) : k[X] :=
  Lagrange.nodal univ low

lemma denom_natDegree (nodes : Fin m → k) : (denom nodes).natDegree = m := by
  simp [denom, Lagrange.natDegree_nodal]

noncomputable def nodeWeight (low : Fin K → k) (a : Fin K) : k :=
  Lagrange.nodalWeight univ low a

noncomputable def residueVec (low : Fin K → k) (B f : k[X]) : Fin K → k :=
  fun a => B.eval (low a) * f.eval (low a) * nodeWeight low a

noncomputable def residueBasis (low : Fin K → k) (B : k[X]) (n : ℕ) :
    Matrix (Fin K) (Fin n) k :=
  fun a i => B.eval (low a) * nodeWeight low a * low a ^ (i : ℕ)

noncomputable def cauchy (low : Fin K → k) (border : Fin m → k) :
    Matrix (Fin K) (Fin m) k :=
  fun a j => 1 / (border j - low a)

lemma nodeWeight_ne_zero (low : Fin K → k) (hinj : Function.Injective low) (a : Fin K) :
    nodeWeight low a ≠ 0 :=
  Lagrange.nodalWeight_ne_zero hinj.injOn (mem_univ a)

/-- The first barycentric formula, with the nodal denominator divided out. -/
theorem sum_residue_div (low : Fin K → k) (hinj : Function.Injective low)
    (f : k[X]) (hdeg : f.natDegree < K) (y : k) (hy : ∀ a, y ≠ low a) :
    ∑ a, nodeWeight low a * f.eval (low a) / (y - low a) = f.eval y / (denom low).eval y := by
  have hfi : f = Lagrange.interpolate univ low (fun a => f.eval (low a)) :=
    Lagrange.eq_interpolate hinj.injOn
      (degree_le_natDegree.trans_lt (by simpa using (show
        (f.natDegree : WithBot ℕ) < (K : WithBot ℕ) by exact_mod_cast hdeg)))
  have hb := Lagrange.eval_interpolate_not_at_node
    (s := (univ : Finset (Fin K))) (v := low) (fun a => f.eval (low a))
    (x := y) (fun a _ => hy a)
  rw [← hfi] at hb
  have hd : (denom low).eval y ≠ 0 := Lagrange.eval_nodal_not_at_node (fun a _ => hy a)
  apply (eq_div_iff hd).2
  rw [hb]
  simp only [denom, nodeWeight, div_eq_mul_inv, sum_mul, mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Partial fractions of the residue vector of a polynomial factor. -/
theorem residue_sum (low : Fin K → k) (hinj : Function.Injective low)
    (B f : k[X]) (hdeg : (B * f).natDegree < K)
    (y : k) (hy : ∀ a, y ≠ low a) :
    ∑ a, residueVec low B f a / (y - low a) = B.eval y * f.eval y / (denom low).eval y := by
  have h := sum_residue_div low hinj (B * f) hdeg y hy
  simpa [residueVec, eval_mul, mul_assoc, mul_left_comm, mul_comm] using h

/-- The Gram of two residue bases is a low-node Hankel moment matrix. -/
theorem gram_low_entry (low : Fin K → k) (BX BY : k[X]) (i j : Fin n) :
    ((residueBasis low BY n).transpose * residueBasis low BX n) i j =
      ∑ a, (BX.eval (low a) * BY.eval (low a) * nodeWeight low a ^ 2) *
        low a ^ ((i : ℕ) + (j : ℕ)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, residueBasis, pow_add]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem basis_sum (low : Fin K → k) (hinj : Function.Injective low)
    (B : k[X]) (hdeg : B.natDegree + n ≤ K) (i : Fin n)
    (y : k) (hy : ∀ a, y ≠ low a) :
    ∑ a, residueBasis low B n a i / (y - low a) =
      B.eval y * y ^ (i : ℕ) / (denom low).eval y := by
  have hf : (B * X ^ (i : ℕ)).natDegree < K := by
    have h := natDegree_mul_le (p := B) (q := (X : k[X]) ^ (i : ℕ))
    simp only [natDegree_X_pow] at h
    have := i.2
    omega
  have h := residue_sum low hinj B (X ^ (i : ℕ)) hf y hy
  simpa [residueVec, residueBasis, eval_pow, eval_X, mul_assoc, mul_left_comm, mul_comm] using h

noncomputable def cauchyGram (low : Fin K → k) (s : Finset k) (w : k → k) :
    Matrix (Fin K) (Fin K) k :=
  ∑ y ∈ s, w y • Matrix.vecMulVec (fun a => 1 / (y - low a)) (fun a => 1 / (y - low a))

/-- The signed high Gram of residue bases is another Hankel moment matrix. -/
theorem gram_high_entry (low : Fin K → k) (hinj : Function.Injective low)
    (BX BY : k[X]) (hBX : BX.natDegree + n ≤ K) (hBY : BY.natDegree + n ≤ K)
    (s : Finset k) (w : k → k) (hs : ∀ y ∈ s, ∀ a, y ≠ low a) (i j : Fin n) :
    ((residueBasis low BY n).transpose * cauchyGram low s w * residueBasis low BX n) i j =
      ∑ y ∈ s, (w y * BX.eval y * BY.eval y / (denom low).eval y ^ 2) *
        y ^ ((i : ℕ) + (j : ℕ)) := by
  unfold cauchyGram
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.transpose_apply]
  have h1 := basis_sum low hinj BY hBY i y (hs y hy)
  have h2 := basis_sum low hinj BX hBX j y (hs y hy)
  simp only [div_eq_mul_inv] at h1 h2
  have e1 : (∑ a, residueBasis low BY n a i * (1 / (y - low a))) =
      BY.eval y * y ^ (i : ℕ) / (denom low).eval y := by
    simpa [div_eq_mul_inv] using h1
  have e2 : (∑ a, (1 / (y - low a)) * residueBasis low BX n a j) =
      BX.eval y * y ^ (j : ℕ) / (denom low).eval y := by
    simpa [div_eq_mul_inv, mul_comm] using h2
  rw [e1, e2, pow_add]
  ring

end CatalanCore.Linalg.CauchyPolynomial
