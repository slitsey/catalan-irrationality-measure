module
public import CatalanCore.Li2.Decay.Fields
public import CatalanCore.Tools.Joukowski
public import CatalanCore.Lai.DecayEnergy
public import Mathlib.Tactic.Ring
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
open CatalanCore.Tools.Joukowski
noncomputable def T (k : ℕ) (x : ℝ) : ℝ := (Polynomial.Chebyshev.T ℝ (k:ℤ)).eval x
structure SegmentData where
  M : ℂ
  h : ℂ
  h_ne : h ≠ 0
  N : ℕ
  c : ℕ → ℝ
  finite_coeff : ∀ k, N < k → c k=0
noncomputable def SegmentData.ν (d : SegmentData) : Measure ℂ := CatalanCore.Tools.Joukowski.segMeasure d.M d.h d.c d.N
def SegmentData.densityNonneg (d : SegmentData) : Prop :=
  ∀ x ∈ Icc (-1:ℝ) 1, 0 ≤ CatalanCore.Zeta5.Potential.chebF d.c d.N x
noncomputable def SegmentData.ownPolynomial (d : SegmentData) : ℝ[X] :=
  Polynomial.C (d.c 0*(Real.log ‖d.h‖-Real.log 2)) -
    ∑ k ∈ Finset.range d.N, Polynomial.C (d.c (k+1)/(k+1:ℕ))*
      Polynomial.Chebyshev.T ℝ ((k+1:ℕ):ℤ)
noncomputable def fpoly (c : ℕ → ℝ) (N : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (N+1), Polynomial.C (c k:ℂ)*Polynomial.Chebyshev.T ℂ (k:ℤ)
noncomputable def rpoly (c : ℕ → ℝ) (N : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range N, Polynomial.C (c (k+1):ℂ)*Polynomial.Chebyshev.U ℂ (k:ℤ)
noncomputable def Gfun (c : ℕ → ℝ) (N : ℕ) (ζ : ℂ) : ℂ :=
  (c 0:ℂ)*Complex.log (CatalanCore.Tools.Joukowski.jphi ζ/2) -
    ∑ k ∈ Finset.range N, (c (k+1):ℂ)*(CatalanCore.Tools.Joukowski.jphi ζ)⁻¹^(k+1)/(k+1:ℕ)

def HasTaylorSeriesAt (f : ℂ → ℂ) (b : ℕ → ℂ) (x : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ u : ℂ, ‖u‖ < r → HasSum (fun n => b n*u^n) (f (x+u))
def IsDiscSegmentPrimitive (d : SegmentData) (ζ γ : ℂ) (R : ℝ) (G : ℂ → ℂ) : Prop :=
  ∃ L : ℂ → ℂ,
    AnalyticOnNhd ℂ L (Metric.ball 0 R) ∧
    L 0=Complex.log (CatalanCore.Tools.Joukowski.jphi ζ/2) ∧
    (∀ u ∈ Metric.ball (0:ℂ) R, 1 < CatalanCore.Tools.Joukowski.jc (ζ+γ*u) ∧
      Complex.exp (L u)=CatalanCore.Tools.Joukowski.jphi (ζ+γ*u)/2 ∧
      G u=(d.c 0:ℂ)*L u -
        ∑ k ∈ Finset.range d.N, (d.c (k+1):ℂ)*(CatalanCore.Tools.Joukowski.jphi (ζ+γ*u))⁻¹^(k+1)/(k+1:ℕ))
def IsLocalSegmentPrimitive (d : SegmentData) (ζ : ℂ) (G : ℂ → ℂ) : Prop :=
  ∃ R : ℝ, 0 < R ∧
    IsDiscSegmentPrimitive d ζ 1 R (fun u => G (ζ+u))
theorem segPot_closed_own (d : SegmentData) (hpos : d.densityNonneg)
    (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    P d.ν (d.M+d.h*(x:ℂ)) = d.c 0*(Real.log ‖d.h‖-Real.log 2)-
      ∑ k ∈ Finset.range d.N, d.c (k+1)*T (k+1) x/(k+1:ℕ) := by
  have hh := (CatalanCore.Lai.DecayEnergy.potC_seg_inside (M:=d.M) d.h_ne hpos hx).2
  change P d.ν (d.M+d.h*(x:ℂ)) = _ at hh
  rw [hh]
  simp only [T,mul_sub]
  apply congrArg₂ (fun a b : ℝ => a-b)
  · ring
  · apply Finset.sum_congr rfl
    intro k hk
    ring

theorem segPot_closed (d : SegmentData) (hpos : d.densityNonneg) (s : ℂ)
    (hs : 1 < jc ((s-d.M)/d.h)) :
    P d.ν s=d.c 0*Real.log ‖d.h‖+(Gfun d.c d.N ((s-d.M)/d.h)).re := by
  have hh := logPotC_segMeasure d.h_ne hpos hs
  have heq : P d.ν s = -logPotC d.ν s := by simp [P,logPotC]
  rw [heq,SegmentData.ν,hh]
  have hn : ‖jphi ((s-d.M)/d.h)/(2:ℂ)‖=jR ((s-d.M)/d.h)/2 := by
    rw [norm_div,← jR_eq_norm hs]
    norm_num
  simp only [Gfun,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.re_sum,Complex.div_natCast_re,Complex.log_re,hn,inv_pow]
  ring
theorem zeta_sub_jq (ζ : ℂ) (hs : 1 < jc ζ) : ζ-jq ζ=(jphi ζ)⁻¹ := by
  have h := (jphi_spec hs).2
  change (jphi ζ+(jphi ζ)⁻¹)/2=ζ at h
  dsimp [jq]
  linear_combination -h

theorem cheb_jphi_identity (ζ : ℂ) (hs : 1 < jc ζ) (k : ℕ) :
    (Chebyshev.T ℂ ((k+1:ℕ):ℤ)).eval ζ-jq ζ*(Chebyshev.U ℂ (k:ℤ)).eval ζ =
      (jphi ζ)⁻¹^(k+1) := by
  induction k with
  | zero => simpa using zeta_sub_jq ζ hs
  | succ k ih =>
    have ht : (Chebyshev.T ℂ ((k+2:ℕ):ℤ)).eval ζ =
        ζ*(Chebyshev.T ℂ ((k+1:ℕ):ℤ)).eval ζ-
          (1-ζ^2)*(Chebyshev.U ℂ (k:ℤ)).eval ζ := by
      simpa only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_X,
        Polynomial.eval_one,Polynomial.eval_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using
        congrArg (Polynomial.eval ζ) (Chebyshev.T_eq_X_mul_T_sub_pol_U ℂ (k:ℤ))
    have hu : (Chebyshev.U ℂ ((k+1:ℕ):ℤ)).eval ζ =
        ζ*(Chebyshev.U ℂ (k:ℤ)).eval ζ+(Chebyshev.T ℂ ((k+1:ℕ):ℤ)).eval ζ := by
      simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
        Nat.cast_add,Nat.cast_one] using
        congrArg (Polynomial.eval ζ) (Chebyshev.U_eq_X_mul_U_add_T ℂ (k:ℤ))
    change (Chebyshev.T ℂ ((k+2:ℕ):ℤ)).eval ζ-
      jq ζ*(Chebyshev.U ℂ ((k+1:ℕ):ℤ)).eval ζ = (jphi ζ)⁻¹^(k+2)
    calc
      _ = (ζ-jq ζ)*((Chebyshev.T ℂ ((k+1:ℕ):ℤ)).eval ζ-
          jq ζ*(Chebyshev.U ℂ (k:ℤ)).eval ζ) := by
        rw [ht,hu]
        linear_combination -(Chebyshev.U ℂ (k:ℤ)).eval ζ*(jq_sq hs)
      _ = _ := by rw [zeta_sub_jq ζ hs,ih,pow_succ]; ring

theorem segment_poly_quotient (d : SegmentData) (ζ : ℂ) (hs : 1 < jc ζ) :
    (fpoly d.c d.N).eval ζ/jq ζ-(rpoly d.c d.N).eval ζ =
      ((d.c 0:ℂ)+∑ k ∈ Finset.range d.N,
        (d.c (k+1):ℂ)*(jphi ζ)⁻¹^(k+1))/jq ζ := by
  classical
  have hq := jq_ne_zero hs
  apply (eq_div_iff hq).2
  simp only [sub_mul,div_mul_cancel₀ _ hq]
  simp only [fpoly,rpoly,Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_C]
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero,Chebyshev.T_zero,Polynomial.eval_one,mul_one]
  rw [Finset.sum_mul]
  have he : (∑ k ∈ Finset.range d.N,
        (d.c (k+1):ℂ)*(Chebyshev.T ℂ ((k+1:ℕ):ℤ)).eval ζ)-
      (∑ k ∈ Finset.range d.N,
        ((d.c (k+1):ℂ)*(Chebyshev.U ℂ (k:ℤ)).eval ζ)*jq ζ) =
      ∑ k ∈ Finset.range d.N, (d.c (k+1):ℂ)*(jphi ζ)⁻¹^(k+1) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hh := congrArg (fun z : ℂ => (d.c (k+1):ℂ)*z) (cheb_jphi_identity ζ hs k)
    linear_combination hh
  linear_combination he

theorem segPot_hasDerivAt (d : SegmentData) (ζ : ℂ) (hs : 1 < jc ζ)
    (G : ℂ → ℂ) (hG : IsLocalSegmentPrimitive d ζ G) :
    HasDerivAt G ((fpoly d.c d.N).eval ζ/jq ζ-(rpoly d.c d.N).eval ζ) ζ := by
  classical
  rcases hG with ⟨R,hR,L,hLan,hLzero,hbranch⟩
  have hL : HasDerivAt L (deriv L 0) 0 :=
    (hLan 0 (Metric.mem_ball_self hR)).differentiableAt.hasDerivAt
  have hD : HasDerivAt (fun y : ℂ => L (y-ζ)) (deriv L 0) ζ := by
    have hsub : HasDerivAt (fun y : ℂ => y-ζ) 1 ζ := (hasDerivAt_id' ζ).sub_const ζ
    have hLz : HasDerivAt L (deriv L 0) ((fun y : ℂ => y-ζ) ζ) := by
      simpa only [sub_self] using hL
    simpa only [mul_one,Function.comp_def] using
      HasDerivAt.comp ζ (h:=fun y : ℂ => y-ζ) hLz hsub
  have hevent : ∀ᶠ y : ℂ in nhds ζ, Complex.exp (L (y-ζ))=jphi y/2 ∧
      G y=(d.c 0:ℂ)*L (y-ζ)-∑ k ∈ Finset.range d.N,
        (d.c (k+1):ℂ)*(jphi y)⁻¹^(k+1)/(k+1:ℕ) := by
    filter_upwards [Metric.ball_mem_nhds ζ hR] with y hy
    have hy0 : y-ζ ∈ Metric.ball (0:ℂ) R := by
      simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hy
    have hh := (hbranch (y-ζ) hy0).2
    have heq : ζ+(y-ζ)=y := by ring
    simpa only [one_mul,heq] using hh
  have hE : HasDerivAt (fun y : ℂ => Complex.exp (L (y-ζ)))
      (Complex.exp (L 0)*deriv L 0) ζ := by simpa only [sub_self] using hD.cexp
  have hE' : HasDerivAt (fun y : ℂ => jphi y/2) (jphi ζ/jq ζ/2) ζ :=
    (hasDerivAt_jphi hs).div_const 2
  have hder : Complex.exp (L 0)*deriv L 0=jphi ζ/jq ζ/2 :=
    (hE.congr_of_eventuallyEq (hevent.mono (fun y hy => hy.1.symm))).unique hE'
  have hvalue : Complex.exp (L 0)=jphi ζ/2 := by
    simpa only [sub_self] using (Filter.Eventually.self_of_nhds hevent).1
  have hDvalue : deriv L 0=(jq ζ)⁻¹ := by
    rw [hvalue] at hder
    have hφ := jphi_ne_zero hs
    apply mul_left_cancel₀ (div_ne_zero hφ (by norm_num : (2:ℂ)≠0))
    rw [hder]
    ring
  have hD' : HasDerivAt (fun y : ℂ => L (y-ζ)) (jq ζ)⁻¹ ζ := by
    rw [← hDvalue]
    exact hD
  have hterm (k : ℕ) : HasDerivAt
      (fun y : ℂ => (d.c (k+1):ℂ)*(jphi y)⁻¹^(k+1)/(k+1:ℕ))
      (-(d.c (k+1):ℂ)*(jphi ζ)⁻¹^(k+1)/jq ζ) ζ := by
    have hh := ((hasDerivAt_jphi_inv_pow hs (k+1)).const_mul (d.c (k+1):ℂ)).div_const (k+1:ℕ)
    simp only [← inv_pow] at hh
    convert hh using 1
    field_simp <;> ring
  have hsum : HasDerivAt (fun y : ℂ => ∑ k ∈ Finset.range d.N,
      (d.c (k+1):ℂ)*(jphi y)⁻¹^(k+1)/(k+1:ℕ))
      (∑ k ∈ Finset.range d.N, -(d.c (k+1):ℂ)*(jphi ζ)⁻¹^(k+1)/jq ζ) ζ :=
    HasDerivAt.fun_sum (fun k _ => hterm k)
  have hfinal := (hD'.const_mul (d.c 0:ℂ)).sub hsum
  have hfinal' := hfinal.congr_of_eventuallyEq (hevent.mono (fun y hy => hy.2))
  convert hfinal' using 1
  rw [segment_poly_quotient d ζ hs]
  simp only [Finset.sum_div,add_div,div_eq_mul_inv,neg_mul,neg_div,
    Finset.sum_neg_distrib,add_mul,Finset.sum_mul]
  ring

#print axioms segPot_closed_own
#print axioms segPot_closed
#print axioms segPot_hasDerivAt
end CatalanCore.Li2.DecayCert
