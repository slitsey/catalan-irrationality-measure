module
public import CatalanMeasure.Parametric.SecondaryTentFilteredResponse
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Algebra.Ring.GeomSum
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators Nat
noncomputable section

/-- Reversed coefficients of the exact factor basis are Newton binomials.
Pascal induction avoids division by characteristic-dependent indices. -/
theorem secondaryTent_reversed_power_coeff {p : ℕ} [hp : Fact p.Prime]
    (k : ℕ) : k < p → ∀ e, e < p →
    ((X-1 : (ZMod p)[X])^(p-1-k)).coeff (p-1-e) = (e.choose k : ZMod p) := by
  induction k with
  | zero =>
    intro hk e he
    have hg : (X-1 : (ZMod p)[X])^(p-1) =
        ∑ i ∈ Finset.range p, (X : (ZMod p)[X])^i := by
      have hx : (X-1 : (ZMod p)[X]) ≠ 0 := by
        simpa only [Polynomial.C_1] using (X_sub_C_ne_zero (1 : ZMod p))
      apply mul_right_cancel₀ hx
      rw [geom_sum_mul, ← pow_succ, Nat.sub_add_cancel hp.out.pos]
      simpa using (sub_pow_char (X : (ZMod p)[X]) 1)
    rw [Nat.sub_zero, hg]
    have hn : p-1-e < p := by omega
    simp [Polynomial.finsetSum_coeff, coeff_X_pow, Finset.sum_ite_eq', hn]
  | succ k ih =>
    intro hk e he
    have hpow : (X-1 : (ZMod p)[X]) * (X-1)^(p-1-(k+1)) =
        (X-1)^(p-1-k) := by
      rw [← pow_succ']
      congr 1
      omega
    induction e with
    | zero =>
      have hd : ((X-1 : (ZMod p)[X])^(p-1-(k+1))).natDegree < p-1 := by
        have hd := natDegree_pow_le (p := (X-1 : (ZMod p)[X]))
          (n := p-1-(k+1))
        have hb : (X-1 : (ZMod p)[X]).natDegree = 1 := by
          simpa only [Polynomial.C_1] using (natDegree_X_sub_C (1 : ZMod p))
        rw [hb, mul_one] at hd
        omega
      simpa using coeff_eq_zero_of_natDegree_lt hd
    | succ e ihe =>
      have he0 : e < p := by omega
      have hn : p-2-e+1 = p-1-e := by omega
      have hn' : p-2-e = p-1-(e+1) := by omega
      have hc := congrArg (fun Q : (ZMod p)[X] => Q.coeff (p-2-e+1)) hpow
      rw [sub_mul, one_mul, coeff_sub, coeff_X_mul, hn, ih (by omega) e he0,
        ihe he0, hn'] at hc
      rw [Nat.choose_succ_succ, Nat.cast_add]
      linear_combination hc

def secondaryTentNewtonPolynomial (p k : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  C ((k ! : ZMod p)⁻¹) * descPochhammer (ZMod p) k

theorem secondaryTent_newton_eval {p k : ℕ} [hp : Fact p.Prime] (hk : k < p) (e : ℕ) :
    (secondaryTentNewtonPolynomial p k).eval (e : ZMod p) = (e.choose k : ZMod p) := by
  have hf : (k ! : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff (k !) p).mp hz
    have := hp.out.dvd_factorial.mp hd
    omega
  rw [secondaryTentNewtonPolynomial, eval_mul, eval_C,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul]
  exact inv_mul_cancel_left₀ hf _

theorem secondaryTent_newton_degree {p : ℕ} [Fact p.Prime] (k : ℕ) :
    (secondaryTentNewtonPolynomial p k).natDegree ≤ k := by
  exact (natDegree_C_mul_le _ _).trans (descPochhammer_natDegree _ _).le

def secondaryTentResponseInput (p N : ℕ) [Fact p.Prime] (c : Fin N → ZMod p) : (ZMod p)[X] :=
  ∑ k : Fin N, C (c k) * (X-1)^(p-1-k.val)

def secondaryTentResponsePolynomial (p N : ℕ) [Fact p.Prime]
    (c : Fin N → ZMod p) : (ZMod p)[X] :=
  ∑ k : Fin N, C (c k) * secondaryTentNewtonPolynomial p k.val

theorem secondaryTent_response_input_degree {p N : ℕ} [hp : Fact p.Prime]
    (c : Fin N → ZMod p) : (secondaryTentResponseInput p N c).natDegree < p := by
  have hb : (secondaryTentResponseInput p N c).natDegree ≤ p-1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    have hd := (natDegree_C_mul_le (c k) ((X-1 : (ZMod p)[X])^(p-1-k.val))).trans
      (natDegree_pow_le (p := (X-1 : (ZMod p)[X])) (n := p-1-k.val))
    have hb : (X-1 : (ZMod p)[X]).natDegree = 1 := by
      simpa only [Polynomial.C_1] using (natDegree_X_sub_C (1 : ZMod p))
    rw [hb, mul_one] at hd
    omega
  have := hp.out.pos
  omega

theorem secondaryTent_response_polynomial_degree {p N : ℕ} [Fact p.Prime]
    (hN : 0 < N) (c : Fin N → ZMod p) :
    (secondaryTentResponsePolynomial p N c).natDegree < N := by
  apply lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ _)
    (show N-1 < N by omega)
  intro k hk
  exact (natDegree_C_mul_le _ _).trans ((secondaryTent_newton_degree k.val).trans (by omega))

theorem secondaryTent_response_input_coeff {p N : ℕ} [Fact p.Prime]
    (hNp : N ≤ p) (c : Fin N → ZMod p) {e : ℕ} (he : e < p) :
    (secondaryTentResponseInput p N c).coeff (p-1-e) =
      (secondaryTentResponsePolynomial p N c).eval (e : ZMod p) := by
  simp only [secondaryTentResponseInput, secondaryTentResponsePolynomial,
    Polynomial.finsetSum_coeff, coeff_C_mul, eval_finset_sum, eval_mul, eval_C]
  apply Finset.sum_congr rfl
  intro k hk
  rw [secondaryTent_reversed_power_coeff _ (by omega) _ he,
    secondaryTent_newton_eval (by omega)]

theorem secondaryTent_response_input_factor {p N : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hNp : N ≤ p) (c : Fin N → ZMod p) :
    (X-1 : (ZMod p)[X])^(p-N) ∣ secondaryTentResponseInput p N c := by
  refine ⟨∑ k : Fin N, C (c k)*(X-1)^(N-1-k.val), ?_⟩
  rw [secondaryTentResponseInput, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_left_comm, ← pow_add]
  congr 2
  omega

theorem secondaryTent_response_input_injective {p N : ℕ} [Fact p.Prime]
    (hNp : N ≤ p) : Function.Injective (secondaryTentResponseInput p N) := by
  intro c d h
  have hcomp := congrArg (fun Q : (ZMod p)[X] => Q.comp (X+1)) h
  simp only [secondaryTentResponseInput, Polynomial.sum_comp,
    mul_comp, C_comp, pow_comp, sub_comp, X_comp, one_comp,
    add_sub_cancel_right] at hcomp
  have hc (a : Fin N → ZMod p) (k : Fin N) :
      (∑ j : Fin N, C (a j)*(X : (ZMod p)[X])^(p-1-j.val)).coeff
        (p-1-k.val) = a k := by
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
    · simp
    · intro j hj hjk
      have hexp : p-1-j.val ≠ p-1-k.val := by
        intro heq
        have hj := j.isLt
        have hk := k.isLt
        have hval : j.val = k.val := by omega
        exact hjk (Fin.ext hval)
      simp [coeff_C_mul, coeff_X_pow, hexp, Ne.symm hexp]
    · simp
  funext k
  have hh := congrArg (fun Q : (ZMod p)[X] => Q.coeff (p-1-k.val)) hcomp
  simpa only [hc] using hh

end
end CatalanMeasure.Parametric
