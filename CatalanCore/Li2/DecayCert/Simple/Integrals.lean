module
public import CatalanCore.Li2.DecayCert.Lattice.Primitive
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 800000
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.Simple
open CatalanCore.Li2.Decay
noncomputable section

theorem omega_closed (z x : ℝ) :
    omega z x=2*x*Real.log x-3*(x-1)*Real.log (x-1)-(4-x)*Real.log (4-x)+1-x*Real.log |z| := by
  unfold omega
  rw [show -(x:ℂ)=((-x:ℝ):ℂ) by simp,phi0_real_closed]
  have h1 : -x+1= -(x-1) := by ring
  have h4 : -x+4=4-x := by ring
  rw [h1,h4,Real.log_neg_eq_log,Real.log_neg_eq_log]
  ring

def atomApprox (z rho theta : ℝ) (p : ℝ[X]) (x : ℝ) : ℝ :=
  omega z x-rho-theta-2*p.eval x

def atomPrimitive (z rho theta : ℝ) (p : ℝ[X]) (x : ℝ) : ℝ :=
  2*Gtilde x-3*Gtilde (x-1)+Gtilde (4-x)+(1-rho-theta)*x-
    Real.log |z| *x^2/2-2*p.integral.eval x

theorem atomApprox_continuous (z rho theta : ℝ) (p : ℝ[X]) :
    Continuous (atomApprox z rho theta p) := by
  exact (((continuous_phi0_neg.sub (continuous_id.mul continuous_const)).sub continuous_const).sub
    continuous_const).sub (p.continuous.const_mul 2)

theorem atomPrimitive_continuous (z rho theta : ℝ) (p : ℝ[X]) :
    Continuous (atomPrimitive z rho theta p) := by
  exact (((((Gtilde_continuous.const_mul 2).sub
    ((Gtilde_continuous.comp (continuous_id.sub continuous_const)).const_mul 3)).add
    (Gtilde_continuous.comp (continuous_const.sub continuous_id))).add
    (continuous_const.mul continuous_id)).sub
    ((continuous_const.mul (continuous_id.pow 2)).div_const 2)).sub (p.integral.continuous.const_mul 2)

theorem atomPrimitive_hasDerivAt (z rho theta : ℝ) (p : ℝ[X]) (x : ℝ)
    (hx : x∈Ioo (1:ℝ) 4) :
    HasDerivAt (atomPrimitive z rho theta p) (atomApprox z rho theta p x) x := by
  have h0:=Gtilde_hasDerivAt x (by linarith [hx.1])
  have h1:=(Gtilde_hasDerivAt (x-1) (by linarith [hx.1])).comp x ((hasDerivAt_id x).sub_const 1)
  have h4:=(Gtilde_hasDerivAt (4-x) (by linarith [hx.2])).comp x ((hasDerivAt_const x 4).sub (hasDerivAt_id x))
  have hd:=(((((h0.const_mul 2).sub (h1.const_mul 3)).add h4).add
    ((hasDerivAt_id x).const_mul (1-rho-theta))).sub
    ((((hasDerivAt_id x).pow 2).const_mul (Real.log |z|)).div_const 2)).sub
    ((p.integral.hasDerivAt x).const_mul 2)
  convert hd using 1
  · rfl
  · rw [atomApprox,omega_closed]
    simp only [id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,
      Polynomial.derivative_integral]
    ring

theorem integral_A_closed (z rho theta p q : ℝ) (d : DualDatum) (poly : ℝ[X])
    (hpq : 1≤p ∧ p≤q ∧ q≤4) (R : ℝ)
    (hR : ∀x∈Icc p q,|U d.σ (-(x:ℂ))-poly.eval x|≤R) :
    |(∫x in p..q,A z rho d.σ x-theta)-
      (atomPrimitive z rho theta poly q-atomPrimitive z rho theta poly p)|≤2*R*(q-p) := by
  let err : ℝ→ℝ:=fun x=>U d.σ (-(x:ℂ))-poly.eval x
  have hactual : Continuous (fun x=>A z rho d.σ x-theta) :=
    (continuous_A_real z rho d).sub continuous_const
  have happ:=atomApprox_continuous z rho theta poly
  have herr : Continuous err := by
    convert (happ.sub hactual).div_const 2 using 1
    funext x
    simp only [Pi.div_apply, Pi.sub_apply, err, atomApprox, A]
    ring
  have hFTC : (∫x in p..q,atomApprox z rho theta poly x)=
      atomPrimitive z rho theta poly q-atomPrimitive z rho theta poly p := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpq.2.1
      (atomPrimitive_continuous z rho theta poly).continuousOn _ (happ.intervalIntegrable _ _)
    intro x hx
    exact atomPrimitive_hasDerivAt z rho theta poly x ⟨by linarith [hx.1,hpq.1],by linarith [hx.2,hpq.2.2]⟩
  have hefield : (fun x=>A z rho d.σ x-theta)=fun x=>atomApprox z rho theta poly x-2*err x := by
    funext x
    simp only [atomApprox,A,err]
    ring
  have heI : (∫x in p..q,A z rho d.σ x-theta)=
      (∫x in p..q,atomApprox z rho theta poly x)-2*(∫x in p..q,err x) := by
    rw [hefield,intervalIntegral.integral_sub (happ.intervalIntegrable _ _) ((herr.intervalIntegrable _ _).const_mul 2),
      intervalIntegral.integral_const_mul]
  have hb:=intervalIntegral.norm_integral_le_of_norm_le_const (a:=p) (b:=q) (f:=err) (C:=R) (by
    intro x hx
    have hx' : x∈Ioc p q := by simpa only [uIoc_of_le hpq.2.1] using hx
    exact hR x ⟨hx'.1.le,hx'.2⟩)
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hpq.2.1)] at hb
  rw [heI,hFTC]
  rw [show (atomPrimitive z rho theta poly q-atomPrimitive z rho theta poly p)-
    2*(∫x in p..q,err x)-(atomPrimitive z rho theta poly q-atomPrimitive z rho theta poly p)=
    -2*(∫x in p..q,err x) by ring]
  rw [abs_mul,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith
#print axioms omega_closed
#print axioms atomPrimitive_hasDerivAt
#print axioms integral_A_closed
end
end CatalanCore.Li2.DecayCert.Simple
