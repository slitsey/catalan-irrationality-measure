module
public import CatalanMeasure.GenD.Uniform.Prefix.RawResponsePhi
public import CatalanMeasure.GenD.Uniform.Prefix.LowFilter
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Finset
variable {R : Type*} [CommRing R]

 theorem pstep_pow_iter (p a : ℕ) (f : ℕ→R) (b : ℕ) :
    ((shift^p-1 : Module.End R (ℕ→R))^a) f b=(fwdDiff p)^[a] f b := by
  rw [Module.End.pow_apply]
  have hfun : (⇑(shift^p-1 : Module.End R (ℕ→R)))=fwdDiff p := by
    funext g n
    change (shift^p) g n-g n=g (n+p)-g n
    rw [shift_pow_apply]
  rw [hfun]

/-- The actual p-step operator shifts quotient J by k while leaving the residue
fixed. No quotient bound or factorial inversion appears. -/
theorem pstep_binomial_action (p a J ell : ℕ) (f : ℕ→R) :
    ((shift^p-1 : Module.End R (ℕ→R))^a) f (J*p+ell)=
      ∑ k∈range (a+1),(-1:R)^(a-k)*(a.choose k:R)*f ((J+k)*p+ell) := by
  rw [pstep_pow_iter]
  have hi : ∀k:ℕ,J*p+ell+k*p=(J+k)*p+ell := by intro k;ring
  simpa only [nsmul_eq_mul,mul_one,Nat.cast_id,zsmul_eq_mul,Int.cast_mul,Int.cast_pow,
    Int.cast_neg,Int.cast_one,Int.cast_natCast,hi] using
    fwdDiff_iter_eq_sum_shift (h:=p) f a (J*p+ell)

/-- Genuine p-step compression on the fixed-residue covector response. -/
theorem pstep_fixed_residue (p a J ell : ℕ) (hp : 0<p) (hell : ell<p)
    (S : ℤ) (psi : ℕ→ℤ→R) (f e : R) :
    ((shift^p-1 : Module.End R (ℕ→R))^a)
      (fun j => psi (j/p) S*f+(psi (j/p) (S-1)-psi (j/p) S)*e) (J*p+ell)=
      pstepCovector a psi J S*f+
        (pstepCovector a psi J (S-1)-pstepCovector a psi J S)*e := by
  rw [pstep_binomial_action]
  have hj : ∀k:ℕ,((J+k)*p+ell)/p=J+k := by
    intro k
    rw [Nat.add_comm ((J+k)*p) ell,Nat.mul_comm (J+k) p,Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt hell,zero_add]
  simp_rw [hj]
  exact pstep_response_contraction a J S psi f e

#print axioms pstep_binomial_action
#print axioms pstep_fixed_residue
end CatalanMeasure.GenD.Uniform.Prefix


