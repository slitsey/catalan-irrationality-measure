module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Z0.7: first-order compression

If `Q T P = diag τ` over `L⟦X⟧` with `Q P = 1`, and the first-order compression of `T` vanishes on
`ker T₀ × ker T₀ᵀ` (condition `(★)`), then every `τ i` with `τ i (0) = 0` is divisible by `X²`.
Also the number of such `i` is `n - rank T₀`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered

open PowerSeries

variable {L : Type*} [Field L] {n : ℕ}

lemma coeff_one_mul' {R : Type*} [CommRing R] (a b : R⟦X⟧) :
    coeff 1 (a * b) = coeff 1 a * constantCoeff b + constantCoeff a * coeff 1 b := by
  rw [coeff_mul]
  simp [Finset.antidiagonal, add_comm]

/-- The first-order part of a matrix product. -/
lemma map_coeff_one_mul {R : Type*} [CommRing R] (M N : Matrix (Fin n) (Fin n) R⟦X⟧) :
    (M * N).map (coeff 1) = M.map (coeff 1) * N.map constantCoeff
      + M.map constantCoeff * N.map (coeff 1) := by
  refine Matrix.ext fun i k => ?_
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, coeff_one_mul',
    Finset.sum_add_distrib]

lemma map_cc_mul {R : Type*} [CommRing R] (M N : Matrix (Fin n) (Fin n) R⟦X⟧) :
    (M * N).map constantCoeff = M.map constantCoeff * N.map constantCoeff :=
  Matrix.map_mul (f := constantCoeff)

lemma mul_mul_apply_diag {R : Type*} [CommRing R] (A B C : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    (A * B * C) i i = (fun j => A i j) ⬝ᵥ (B *ᵥ fun k => C k i) := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Constant-term consequences of `Q T P = diag τ`, `Q P = 1`. -/
lemma cc_compress (T P Q : Matrix (Fin n) (Fin n) L⟦X⟧) (τ : Fin n → L⟦X⟧)
    (hQP : Q * P = 1) (hd : Q * T * P = diagonal τ) :
    P.map constantCoeff * Q.map constantCoeff = 1 ∧
    T.map constantCoeff * P.map constantCoeff
      = P.map constantCoeff * diagonal (fun i => constantCoeff (τ i)) ∧
    Q.map constantCoeff * T.map constantCoeff
      = diagonal (fun i => constantCoeff (τ i)) * Q.map constantCoeff := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have hQP0 : Q.map constantCoeff * P.map constantCoeff = 1 := by
    rw [← map_cc_mul, hQP]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hPQ0 : P.map constantCoeff * Q.map constantCoeff = 1 := by
    rw [← map_cc_mul, hPQ]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hd0 : Q.map constantCoeff * T.map constantCoeff * P.map constantCoeff
      = diagonal (fun i => constantCoeff (τ i)) := by
    have := congrArg (fun A => A.map constantCoeff) hd
    rw [map_cc_mul, map_cc_mul] at this
    refine this.trans ?_
    refine Matrix.ext fun a b => ?_
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  have hTP : T.map constantCoeff * P.map constantCoeff
      = P.map constantCoeff * diagonal (fun i => constantCoeff (τ i)) := by
    rw [← hd0]
    calc T.map constantCoeff * P.map constantCoeff
        = (P.map constantCoeff * Q.map constantCoeff) * T.map constantCoeff * P.map constantCoeff := by
          rw [hPQ0, one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hQT : Q.map constantCoeff * T.map constantCoeff
      = diagonal (fun i => constantCoeff (τ i)) * Q.map constantCoeff := by
    rw [← hd0]
    calc Q.map constantCoeff * T.map constantCoeff
        = Q.map constantCoeff * T.map constantCoeff * (P.map constantCoeff * Q.map constantCoeff) := by
          rw [hPQ0, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  exact ⟨hPQ0, hTP, hQT⟩

/-- **Z0.7.** Small eigenvalues are divisible by `X²` under the first-order condition `(★)`. -/
theorem X_sq_dvd_of_compress (T P Q : Matrix (Fin n) (Fin n) L⟦X⟧) (τ : Fin n → L⟦X⟧)
    (hQP : Q * P = 1) (hd : Q * T * P = diagonal τ)
    (hstar : ∀ x y : Fin n → L, T.map constantCoeff *ᵥ x = 0 → y ᵥ* T.map constantCoeff = 0 →
      y ⬝ᵥ (T.map (coeff 1) *ᵥ x) = 0) :
    ∀ i, constantCoeff (τ i) = 0 → X ^ 2 ∣ τ i := by
  intro i hi
  obtain ⟨hPQ0, hTP, hQT⟩ := cc_compress T P Q τ hQP hd
  have hd1 := congrArg (fun A => A.map (coeff 1)) hd
  simp only [map_coeff_one_mul] at hd1
  have e := congrFun (congrFun hd1 i) i
  have hx : T.map constantCoeff *ᵥ (fun k => P.map constantCoeff k i) = 0 := by
    funext k
    have := congrFun (congrFun hTP k) i
    rw [Matrix.mul_apply, Matrix.mul_diagonal] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [this, hi, mul_zero]
  have hy : (fun j => Q.map constantCoeff i j) ᵥ* T.map constantCoeff = 0 := by
    funext k
    have := congrFun (congrFun hQT i) k
    rw [Matrix.mul_apply, Matrix.diagonal_mul] at this
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    rw [this, hi, zero_mul]
  have hmid := hstar _ _ hx hy
  have t1 : (Q.map (coeff 1) * T.map constantCoeff * P.map constantCoeff) i i = 0 := by
    rw [Matrix.mul_assoc, hTP, ← Matrix.mul_assoc, Matrix.mul_diagonal, hi, mul_zero]
  have t3 : (Q.map constantCoeff * T.map constantCoeff * P.map (coeff 1)) i i = 0 := by
    rw [hQT, Matrix.mul_assoc, Matrix.diagonal_mul, hi, zero_mul]
  have t2 : (Q.map constantCoeff * T.map (coeff 1) * P.map constantCoeff) i i = 0 := by
    rw [mul_mul_apply_diag]; exact hmid
  rw [map_cc_mul] at e
  simp only [Matrix.add_mul, Matrix.add_apply, t1, t2, t3, add_zero] at e
  have e2 : ((diagonal τ).map (coeff 1)) i i = coeff 1 (τ i) := by simp
  rw [X_pow_dvd_iff]
  intro m hm
  interval_cases m
  · simpa using hi
  · rw [← e2, ← e]

open scoped Classical in
/-- **Z0.7 (count).** The number of vanishing constant terms is `n - rank T(0)`. -/
theorem card_small (T P Q : Matrix (Fin n) (Fin n) L⟦X⟧) (τ : Fin n → L⟦X⟧)
    (hQP : Q * P = 1) (hd : Q * T * P = diagonal τ) :
    (univ.filter fun i => constantCoeff (τ i) = 0).card + (T.map constantCoeff).rank = n := by
  obtain ⟨hPQ0, hTP, -⟩ := cc_compress T P Q τ hQP hd
  have hQP0 : Q.map constantCoeff * P.map constantCoeff = 1 := by
    rw [← map_cc_mul, hQP]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hu : IsUnit (P.map constantCoeff).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 ⟨⟨_, _, hPQ0, hQP0⟩, rfl⟩
  have h1 : (T.map constantCoeff).rank = (diagonal (fun i => constantCoeff (τ i))).rank := by
    rw [← rank_mul_eq_left_of_isUnit_det _ _ hu, hTP, rank_mul_eq_right_of_isUnit_det _ _ hu]
  rw [h1, rank_diagonal, Fintype.card_subtype]
  simpa using Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i => constantCoeff (τ i) = 0)

end CatalanCore.Bordered
