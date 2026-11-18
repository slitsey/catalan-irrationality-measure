module
public import CatalanCore.Li2.DecayCert.Lattice.Bernstein.Range
public import Mathlib.RingTheory.Polynomial.Bernstein
@[expose] public section
set_option Elab.async false
open Polynomial
open scoped BigOperators
open CatalanCore.Uniform.Decay.Tools
namespace CatalanCore.Li2.DecayCert.BernsteinGrid

theorem basis_lower_weight (n k : ℕ) (hk : k≤n+1) (t : ℚ) :
    (((n+1-k:ℕ):ℚ)/((n+1:ℕ):ℚ))*bw (n+1) k t=(1-t)*bw n k t := by
  by_cases hkn : k≤n
  · have hc := Nat.choose_mul_succ_eq n k
    have hcQ : ((n+1).choose k:ℚ)*((n+1-k:ℕ):ℚ)=
        (n.choose k:ℚ)*((n+1:ℕ):ℚ) := by exact_mod_cast hc.symm
    have hn : ((n+1:ℕ):ℚ)≠0 := by positivity
    have hratio : (((n+1-k:ℕ):ℚ)*((n+1).choose k:ℚ))/((n+1:ℕ):ℚ)=(n.choose k:ℚ) := by
      apply (div_eq_iff hn).2
      nlinarith only [hcQ]
    calc
      _=((((n+1-k:ℕ):ℚ)*((n+1).choose k:ℚ))/((n+1:ℕ):ℚ))*t^k*(1-t)^(n+1-k) := by unfold bw; ring
      _=(n.choose k:ℚ)*t^k*(1-t)^(n+1-k) := by rw [hratio]
      _=(1-t)*bw n k t := by
        rw [show n+1-k=n-k+1 by omega,pow_succ]
        unfold bw
        ring
  · have he : k=n+1 := by omega
    subst k
    simp [bw,Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)]

theorem basis_upper_weight (n k : ℕ) (hk : k≤n) (t : ℚ) :
    (((k+1:ℕ):ℚ)/((n+1:ℕ):ℚ))*bw (n+1) (k+1) t=t*bw n k t := by
  have hc := Nat.add_one_mul_choose_eq n k
  have hcQ : ((n+1).choose (k+1):ℚ)*((k+1:ℕ):ℚ)=
      (n.choose k:ℚ)*((n+1:ℕ):ℚ) := by exact_mod_cast hc.symm.trans (Nat.mul_comm _ _)
  have hn : ((n+1:ℕ):ℚ)≠0 := by positivity
  have hratio : (((k+1:ℕ):ℚ)*((n+1).choose (k+1):ℚ))/((n+1:ℕ):ℚ)=(n.choose k:ℚ) := by
    apply (div_eq_iff hn).2
    nlinarith only [hcQ]
  calc
    _=((((k+1:ℕ):ℚ)*((n+1).choose (k+1):ℚ))/((n+1:ℕ):ℚ))*t^(k+1)*(1-t)^(n+1-(k+1)) := by unfold bw; ring
    _=(n.choose k:ℚ)*t^(k+1)*(1-t)^(n-k) := by rw [hratio,Nat.add_sub_add_right]
    _=t*bw n k t := by rw [pow_succ]; unfold bw; ring

noncomputable def bernPoly (n : ℕ) (c : Fin (n+1)→ℚ) : ℚ[X] :=
  ∑ i, c i • bernsteinPolynomial ℚ n i

theorem bernPoly_eval (n : ℕ) (c : Fin (n+1)→ℚ) (t : ℚ) :
    (bernPoly n c).eval t=∑ i,c i*bw n i t := by
  unfold bernPoly
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Polynomial.eval_smul,smul_eq_mul,bernsteinPolynomial,bw,
    Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_one,
    Polynomial.eval_X,Polynomial.eval_natCast]

theorem bernPoly_injective (n : ℕ) : Function.Injective (bernPoly n) := by
  intro c d h
  have hl := bernsteinPolynomial.linearIndependent n
  apply (linearIndependent_iff_injective_fintypeLinearCombination.mp hl)
  simpa only [Fintype.linearCombination_apply,bernPoly] using h

#print axioms basis_lower_weight
#print axioms basis_upper_weight
#print axioms bernPoly_injective
def blendCoeff (n k : ℕ) (c A B : ℚ) (b : ℕ→ℚ) : ℚ :=
  c+(((n+1-k:ℕ):ℚ)/((n+1:ℕ):ℚ))*A*b k+
    ((k:ℚ)/((n+1:ℕ):ℚ))*B*(if k=0 then 0 else b (k-1))

theorem bezier_blend (n : ℕ) (c A B t : ℚ) (b : ℕ→ℚ) :
    (∑ k ∈ Finset.range (n+2),blendCoeff n k c A B b*bw (n+1) k t)=
      c+(A*(1-t)+B*t)*(∑ k ∈ Finset.range (n+1),b k*bw n k t) := by
  have hlo : (∑ k ∈ Finset.range (n+2),b k*
      ((((n+1-k:ℕ):ℚ)/((n+1:ℕ):ℚ))*bw (n+1) k t))=
      (1-t)*(∑ k ∈ Finset.range (n+1),b k*bw n k t) := by
    calc
      _=∑ k ∈ Finset.range (n+2),b k*((1-t)*bw n k t) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [basis_lower_weight n k (by have := Finset.mem_range.mp hk; omega)]
      _=(1-t)*(∑ k ∈ Finset.range (n+2),b k*bw n k t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _=(1-t)*(∑ k ∈ Finset.range (n+1),b k*bw n k t) := by
        rw [Finset.sum_range_succ]
        simp [bw]
  have hhi : (∑ k ∈ Finset.range (n+2),(if k=0 then 0 else b (k-1))*
      (((k:ℚ)/((n+1:ℕ):ℚ))*bw (n+1) k t))=
      t*(∑ k ∈ Finset.range (n+1),b k*bw n k t) := by
    calc
      _=∑ k ∈ Finset.range (n+1),b k*
          ((((k+1:ℕ):ℚ)/((n+1:ℕ):ℚ))*bw (n+1) (k+1) t) := by
        rw [Finset.sum_range_succ']
        simp
      _=∑ k ∈ Finset.range (n+1),b k*(t*bw n k t) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [basis_upper_weight n k (by have := Finset.mem_range.mp hk; omega)]
      _=t*(∑ k ∈ Finset.range (n+1),b k*bw n k t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
  have he (k : ℕ) : blendCoeff n k c A B b*bw (n+1) k t=
      c*bw (n+1) k t+A*(b k*((((n+1-k:ℕ):ℚ)/((n+1:ℕ):ℚ))*bw (n+1) k t))+
      B*((if k=0 then 0 else b (k-1))*(((k:ℚ)/((n+1:ℕ):ℚ))*bw (n+1) k t)) := by
    unfold blendCoeff
    ring
  simp_rw [he,Finset.sum_add_distrib]
  rw [← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,sum_bw,hlo,hhi]
  ring

#print axioms bezier_blend
end CatalanCore.Li2.DecayCert.BernsteinGrid
