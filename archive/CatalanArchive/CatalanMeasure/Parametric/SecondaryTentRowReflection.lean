module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowInputInjective
public import Mathlib.Algebra.Polynomial.Reverse
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

private theorem secondaryTent_reflect_sum {K : Type*} [CommRing K]
    (d : ℕ) (s : Finset ℕ) (f : ℕ → K[X]) :
    reflect d (∑ k ∈ s, f k) = ∑ k ∈ s, reflect d (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, reflect_add, ih]

private theorem secondaryTent_reflect_pow {K : Type*} [CommRing K]
    (d k : ℕ) (f ε : K[X]) (hf : f.natDegree ≤ d)
    (he : reflect d f = ε*f) :
    reflect (d*k) (f^k) = ε^k*f^k := by
  induction k with
  | zero => simp [reflect_one]
  | succ k ih =>
    rw [pow_succ, Nat.mul_succ, reflect_mul _ _
      (natDegree_pow_le.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left k hf)) hf,
      ih, he, pow_succ]
    ring

private theorem secondaryTent_reflect_quadratic {K : Type*} [CommRing K] :
    reflect 2 (X^2+1 : K[X]) = X^2+1 := by
  rw [reflect_add, reflect_monomial, reflect_one]
  rw [revAt_le (by decide : 2 ≤ 2)]
  norm_num <;> ring

private theorem secondaryTent_reflect_doubleX {K : Type*} [CommRing K] :
    reflect 2 (2*X : K[X]) = 2*X := by
  change reflect 2 (C 2 * X) = C 2 * X
  rw [reflect_C_mul]
  conv_lhs => rw [← pow_one (X : K[X]), reflect_monomial]
  rw [revAt_le (by decide : 1 ≤ 2)]
  norm_num

/-- The actual denominator-cleared x-substitution is reciprocal symmetric
around degree n, for every input polynomial (coefficients beyond n are
discarded by its definition). -/
theorem secondaryTent_rowInput_reflect {K : Type*} [CommRing K]
    (n : ℕ) (I : K[X]) :
    reflect (2*n) (secondaryTentRowInput n I) = secondaryTentRowInput n I := by
  have hq : (X^2+1 : K[X]).natDegree ≤ 2 := by
    simpa using (natDegree_add_le (X^2 : K[X]) 1).trans
      (max_le (natDegree_pow_le_of_le 2 natDegree_X_le) (by simp))
  have hz : (2*X : K[X]).natDegree ≤ 2 := by
    have hh : (2*X : K[X]).natDegree ≤ 1 := by
      simpa using (natDegree_mul_le (p := (2 : K[X])) (q := X)).trans
        (by simpa using (natDegree_X_le (R := K)))
    omega
  unfold secondaryTentRowInput secondaryTentRowHom
  rw [secondaryTent_reflect_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have he : 2*n = 2*k+2*(n-k) := by omega
  have hterm : C (I.coeff k) * (X^2+1)^k * (2*X : K[X])^(n-k) =
      C (I.coeff k) * ((X^2+1)^k * (2*X : K[X])^(n-k)) := by ring
  rw [hterm, reflect_C_mul, he, reflect_mul _ _
    (natDegree_pow_le.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left k hq))
    (natDegree_pow_le.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left (n-k) hz))]
  rw [secondaryTent_reflect_pow 2 k _ 1 hq (by simpa using secondaryTent_reflect_quadratic),
    secondaryTent_reflect_pow 2 (n-k) _ 1 hz (by simpa using secondaryTent_reflect_doubleX)]
  simp

def secondaryTentRowNaturalNumerator {K : Type*} [CommRing K]
    (p d : ℕ) (U V : K[X]) : K[X] :=
  (X-1)^p * secondaryTentRowInput d U + (X+1)^p * secondaryTentRowInput d V

theorem secondaryTent_row_natural_numerator_reflect {K : Type*} [CommRing K]
    (p d : ℕ) (U V : K[X]) :
    reflect (p+2*d) (secondaryTentRowNaturalNumerator p d U V) =
      (-1)^p * (X-1)^p * secondaryTentRowInput d U +
      (X+1)^p * secondaryTentRowInput d V := by
  have hm : (X-1 : K[X]).natDegree ≤ 1 := by simpa using natDegree_X_sub_C_le (1:K)
  have hp : (X+1 : K[X]).natDegree ≤ 1 := by
    exact (natDegree_add_le _ _).trans (max_le natDegree_X_le (by simp))
  have hmr : reflect 1 (X-1 : K[X]) = (-1)*(X-1) := by
    rw [reflect_sub, reflect_one_X, reflect_one]
    ring
  have hpr : reflect 1 (X+1 : K[X]) = 1*(X+1) := by
    rw [reflect_add, reflect_one_X, reflect_one]
    ring
  have hmp : reflect p ((X-1 : K[X])^p) = (-1)^p*(X-1)^p := by
    simpa only [one_mul] using secondaryTent_reflect_pow 1 p _ (-1) hm hmr
  have hpp : reflect p ((X+1 : K[X])^p) = (X+1)^p := by
    simpa only [one_mul, one_pow] using secondaryTent_reflect_pow 1 p _ 1 hp hpr
  unfold secondaryTentRowNaturalNumerator
  rw [reflect_add, reflect_mul _ _ (by simpa using natDegree_pow_le_of_le p hm)
    (secondaryTent_rowInput_natDegree d U),
    reflect_mul _ _ (by simpa using natDegree_pow_le_of_le p hp)
      (secondaryTent_rowInput_natDegree d V)]
  rw [hmp, hpp,
    secondaryTent_rowInput_reflect, secondaryTent_rowInput_reflect]

/-- Reflection separates the U and V channels of the actual natural
reconstruction, proving injection without a Cartier or curve library. -/
theorem secondaryTent_row_natural_numerator_zero_iff {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) (p d : ℕ) (hp : Odd p) (U V : K[X])
    (hU : U.natDegree ≤ d) (hV : V.natDegree ≤ d) :
    secondaryTentRowNaturalNumerator p d U V = 0 ↔ U=0 ∧ V=0 := by
  constructor
  · intro h
    have hr := congrArg (reflect (p+2*d)) h
    rw [secondaryTent_row_natural_numerator_reflect, hp.neg_one_pow, reflect_zero] at hr
    have hsum := h
    unfold secondaryTentRowNaturalNumerator at hsum
    have hA : (2:K[X])*((X-1)^p*secondaryTentRowInput d U) = 0 := by
      linear_combination hsum-hr
    have h2p : (2:K[X]) ≠ 0 := by simpa only [← C_ofNat, ne_eq, C_eq_zero] using h2
    have hA₀ := (mul_eq_zero.mp hA).resolve_left h2p
    have hxm : (X-1 : K[X]) ≠ 0 := X_sub_C_ne_zero 1
    have hTU : secondaryTentRowInput d U = 0 :=
      (mul_eq_zero.mp hA₀).resolve_left (pow_ne_zero _ hxm)
    have hTV : secondaryTentRowInput d V = 0 := by
      rw [hTU, mul_zero, zero_add] at hsum
      exact (mul_eq_zero.mp hsum).resolve_left (pow_ne_zero _ (by
        simpa using (X_sub_C_ne_zero (-1:K))))
    exact ⟨(secondaryTent_rowInput_eq_zero_iff h2 d U hU).mp hTU,
      (secondaryTent_rowInput_eq_zero_iff h2 d V hV).mp hTV⟩
  · rintro ⟨rfl,rfl⟩
    simp [secondaryTentRowNaturalNumerator, secondaryTentRowInput, secondaryTentRowHom]

end
end CatalanMeasure.Parametric
