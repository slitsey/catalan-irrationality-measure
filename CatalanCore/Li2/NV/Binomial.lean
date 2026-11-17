module
public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public meta import Lean.Elab.Tactic.Omega

@[expose] public section
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NV
noncomputable section

private def tailPoly (r t : ℕ) : ℚ[X] :=
  ∑ i ∈ Ioc t r, C (Nat.choose r i:ℚ)*X^i*(1-X)^(r-i)

private theorem tail_derivative (r t : ℕ) (ht : t<r) :
    derivative (tailPoly r t) = (r:ℚ[X])*bernsteinPolynomial ℚ (r-1) t := by
  have tel (f : ℕ→ℚ[X]) : ∀ b, t≤b →
      (∑ i ∈ Ioc t b, (f (i-1)-f i))=f t-f b := by
    intro b hb
    induction b,hb using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      rw [Finset.sum_Ioc_succ_top hb,ih]
      simp only [Nat.add_sub_cancel]
      ring
  have hd (i : ℕ) (hi : i∈Ioc t r) :
      derivative (bernsteinPolynomial ℚ r i) =
        (r:ℚ[X])*(bernsteinPolynomial ℚ (r-1) (i-1)-bernsteinPolynomial ℚ (r-1) i) := by
    have hi0 : i≠0 := by have := (Finset.mem_Ioc.mp hi).1;omega
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    simpa only [Nat.succ_sub_one] using bernsteinPolynomial.derivative_succ ℚ r j
  have htail : tailPoly r t = ∑ i∈Ioc t r, bernsteinPolynomial ℚ r i := by
    simp only [tailPoly,bernsteinPolynomial,Polynomial.C_eq_natCast]
  rw [htail,Polynomial.derivative_sum]
  calc
    _ = ∑ i∈Ioc t r, (r:ℚ[X])*(bernsteinPolynomial ℚ (r-1) (i-1)-bernsteinPolynomial ℚ (r-1) i) :=
      Finset.sum_congr rfl hd
    _ = (r:ℚ[X])*(bernsteinPolynomial ℚ (r-1) t-bernsteinPolynomial ℚ (r-1) r) := by
      rw [← Finset.mul_sum,tel _ r ht.le]
    _ = _ := by rw [bernsteinPolynomial.eq_zero_of_lt ℚ (by omega : r-1<r),sub_zero]

private theorem power_expansion (d : ℕ) :
    (1-X : ℚ[X])^d = ∑ j∈range (d+1), C ((-1:ℚ)^j*(Nat.choose d j:ℚ))*X^j := by
  rw [show (1-X:ℚ[X])=(-X)+1 by ring,add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  rw [neg_pow]
  simp only [one_pow,mul_one,map_mul,map_pow,map_neg,map_one,
    Polynomial.C_eq_natCast]
  ring

private theorem factorial_factor (r t : ℕ) (ht : t<r) :
    (r:ℚ)*((r-1).choose t:ℚ)=(r.factorial:ℚ)/((t.factorial:ℚ)*((r-t-1).factorial:ℚ)) := by
  have hn := Nat.choose_mul_factorial_mul_factorial (by omega : t≤r-1)
  have hsub : r-1-t=r-t-1 := by omega
  rw [hsub] at hn
  have hq : ((r-1).choose t:ℚ)*(t.factorial:ℚ)*((r-t-1).factorial:ℚ)=((r-1).factorial:ℚ) := by exact_mod_cast hn
  apply (eq_div_iff (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero t)
    (by exact_mod_cast Nat.factorial_ne_zero (r-t-1)))).2
  calc
    _ = (r:ℚ)*(((r-1).choose t:ℚ)*(t.factorial:ℚ)*((r-t-1).factorial:ℚ)) := by ring
    _ = (r:ℚ)*((r-1).factorial:ℚ) := by rw [hq]
    _ = _ := by exact_mod_cast Nat.mul_factorial_pred (by omega : r≠0)

private def integratedPower (r t : ℕ) : ℚ[X] :=
  ∑ j∈range (r-t), C ((-1:ℚ)^j*(Nat.choose (r-t-1) j:ℚ)/(t+1+j:ℚ))*X^(t+1+j)

private theorem integratedPower_derivative (r t : ℕ) (ht : t<r) :
    derivative (integratedPower r t)=X^t*(1-X)^(r-t-1) := by
  have hr : r-t=(r-t-1)+1 := by omega
  unfold integratedPower
  rw [Polynomial.derivative_sum]
  calc
    _ = ∑ j∈range (r-t), C ((-1:ℚ)^j*(Nat.choose (r-t-1) j:ℚ))*X^(t+j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Polynomial.derivative_C_mul_X_pow]
      have hpow : t+1+j-1=t+j := by omega
      rw [hpow]
      congr 1
      apply congrArg C
      have hj0 : (t+1+j:ℚ)≠0 := by positivity
      simpa only [Nat.cast_add,Nat.cast_one] using div_mul_cancel₀ ((-1:ℚ)^j*(Nat.choose (r-t-1) j:ℚ)) hj0
    _ = X^t*(∑ j∈range (r-t), C ((-1:ℚ)^j*(Nat.choose (r-t-1) j:ℚ))*X^j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_add]
      ring
    _ = _ := by
      apply congrArg (fun p : ℚ[X] => X^t*p)
      calc
        _ = ∑ j∈range ((r-t-1)+1), C ((-1:ℚ)^j*(Nat.choose (r-t-1) j:ℚ))*X^j :=
          Finset.sum_congr (congrArg range hr) (fun _ _ => rfl)
        _ = _ := (power_expansion (r-t-1)).symm

/-- The finite binomial tail, by differentiation and its value at zero. -/
theorem binomial_tail_identity (r t : ℕ) (ht : t<r) :
    (∑ i∈Finset.Ioc t r, C (Nat.choose r i:ℚ)*X^i*(1-X)^(r-i)) =
    C ((r.factorial:ℚ)/((t.factorial:ℚ)*((r-t-1).factorial:ℚ)))*
      ∑ j∈range (r-t), C ((-1:ℚ)^j*(Nat.choose (r-t-1) j:ℚ)/(t+1+j:ℚ))*X^(t+1+j) := by
  let F : ℚ := (r.factorial:ℚ)/((t.factorial:ℚ)*((r-t-1).factorial:ℚ))
  change tailPoly r t=C F*integratedPower r t
  have hd : derivative (tailPoly r t-C F*integratedPower r t)=0 := by
    rw [Polynomial.derivative_sub,tail_derivative r t ht,Polynomial.derivative_C_mul,
      integratedPower_derivative r t ht]
    have hsub : r-1-t=r-t-1 := by omega
    rw [bernsteinPolynomial,hsub]
    dsimp only [F]
    rw [← factorial_factor r t ht]
    simp only [map_mul,Polynomial.C_eq_natCast]
    ring
  have hzero : (tailPoly r t-C F*integratedPower r t).coeff 0=0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C]
    have hL : (tailPoly r t).eval 0=0 := by
      unfold tailPoly
      rw [Polynomial.eval_finsetSum]
      apply Finset.sum_eq_zero
      intro i hi
      have hi0 : i≠0 := by have := (Finset.mem_Ioc.mp hi).1;omega
      simp [hi0]
    have hI : (integratedPower r t).eval 0=0 := by
      unfold integratedPower
      rw [Polynomial.eval_finsetSum]
      apply Finset.sum_eq_zero
      intro j hj
      have hj0 : t+1+j≠0 := by omega
      simp [hj0]
    rw [hL,hI,mul_zero,sub_self]
  have hconst := Polynomial.eq_C_of_derivative_eq_zero hd
  rw [hzero,Polynomial.C_0] at hconst
  exact sub_eq_zero.mp hconst

#print axioms binomial_tail_identity
end
end CatalanCore.Li2.NV

