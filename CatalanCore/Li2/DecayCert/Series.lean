module
public import CatalanCore.Li2.DecayCert.Series.Base
public import CatalanCore.Li2.DecayCert.Arithmetic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
@[expose] public section
set_option Elab.async false
open Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Tools.Joukowski

theorem HasTaylorSeriesAt.monomial_mul {f : ℂ → ℂ} {b : ℕ → ℂ}
    (hb : HasTaylorSeriesAt f b 0) (a : ℂ) (k : ℕ) :
    HasTaylorSeriesAt (fun z => a*z^k*f z)
      (fun n => if k ≤ n then a*b (n-k) else 0) 0 := by
  have hh := (hasTaylorSeriesAt_monomial_zero a k).mul hb
  convert hh using 1
  funext n
  simp [ite_mul,Finset.sum_ite_eq',Nat.lt_succ_iff]

theorem ySeries_ode (ζ γ : ℂ) (hs : 1 < jc ζ) :
    ∀ᶠ u : ℂ in nhds 0,
      (jq ζ)^2*_root_.deriv (fun v : ℂ => (jq (ζ+γ*v))⁻¹) u+
      (2*ζ*γ)*u*_root_.deriv (fun v : ℂ => (jq (ζ+γ*v))⁻¹) u+
      γ^2*u^2*_root_.deriv (fun v : ℂ => (jq (ζ+γ*v))⁻¹) u+
      (γ*ζ)*(jq (ζ+γ*u))⁻¹+γ^2*u*(jq (ζ+γ*u))⁻¹=0 := by
  have hc : Tendsto (fun u : ℂ => ζ+γ*u) (nhds 0) (nhds ζ) := by
    have hcont : Continuous (fun u : ℂ => ζ+γ*u) :=
      continuous_const.add (continuous_const.mul continuous_id')
    simpa using (hcont.continuousAt (x:=(0:ℂ))).tendsto
  filter_upwards [hc.eventually (isOpen_jc.mem_nhds hs)] with u hu
  have hAff : HasDerivAt (fun v : ℂ => ζ+γ*v) γ u := by
    convert ((hasDerivAt_id' u).const_mul γ).const_add ζ using 1 <;> ring
  have hY : HasDerivAt (fun v : ℂ => (jq (ζ+γ*v))⁻¹)
      (-((ζ+γ*u)/jq (ζ+γ*u)*γ)/(jq (ζ+γ*u))^2) u := by
    have hqD : HasDerivAt (fun v : ℂ => jq (ζ+γ*v)) ((ζ+γ*u)/jq (ζ+γ*u)*γ) u := by
      simpa only [Function.comp_def] using
        (hasDerivAt_jq (ζ:=ζ+γ*u) hu).comp u (h:=fun v : ℂ => ζ+γ*v) hAff
    exact hqD.inv (jq_ne_zero hu)
  have hP : (jq ζ)^2+(2*ζ*γ)*u+γ^2*u^2=(jq (ζ+γ*u))^2 := by
    linear_combination (jq_sq hs)-(jq_sq hu)
  calc
    _ = ((jq ζ)^2+(2*ζ*γ)*u+γ^2*u^2)*
        _root_.deriv (fun v : ℂ => (jq (ζ+γ*v))⁻¹) u+
        γ*(ζ+γ*u)*(jq (ζ+γ*u))⁻¹ := by ring
    _ = 0 := by
      rw [hP,hY.deriv]
      field_simp
      ring

theorem ySeries_rec (ζ γ : ℂ) (hs : 1 < jc ζ)
    (y : ℕ → ℂ) (hy : HasTaylorSeriesAt (fun u => (jq (ζ+γ*u))⁻¹) y 0) :
    y 0=(jq ζ)⁻¹ ∧ ∀ n : ℕ,
      (n+1:ℕ)*(jq ζ)^2*y (n+1)=
        -((n:ℂ)+1/2)*(2*ζ*γ)*y n-(n:ℂ)*γ^2*(if n=0 then 0 else y (n-1)) := by
  refine ⟨by simpa using hy.zero,?_⟩
  have hd := hy.deriv
  have hExpr := ((((hd.const_mul ((jq ζ)^2)).add (hd.monomial_mul (2*ζ*γ) 1)).add
    (hd.monomial_mul (γ^2) 2)).add (hy.const_mul (γ*ζ))).add (hy.monomial_mul (γ^2) 1)
  have heq := (hExpr.congr (g:=fun _ : ℂ => 0)
    (by simpa only [pow_one] using ySeries_ode ζ γ hs)).unique (hasTaylorSeriesAt_const 0 0)
  intro n
  have hh := congrFun heq n
  rcases n with _ | n
  · norm_num at hh ⊢
    linear_combination hh
  · rcases n with _ | n
    · norm_num at hh ⊢
      linear_combination hh
    · have h1 : n+1+1-1=n+1 := by omega
      have h2 : n+1+1-2=n := by omega
      have hn1 : 1 ≤ n+1+1 := by omega
      have hn2 : 2 ≤ n+1+1 := by omega
      simp only [hn1,hn2,ite_true,h1,h2] at hh
      simp only [Nat.succ_ne_zero,ite_false] at hh ⊢
      push_cast at hh ⊢
      linear_combination hh
theorem discPrimitive_hasDerivAt (d : SegmentData) (ζ γ : ℂ) (R : ℝ)
    (F : ℂ → ℂ) (hF : IsDiscSegmentPrimitive d ζ γ R F)
    (u : ℂ) (hu : u ∈ Metric.ball 0 R) :
    HasDerivAt F (γ*((fpoly d.c d.N).eval (ζ+γ*u)/jq (ζ+γ*u)-
      (rpoly d.c d.N).eval (ζ+γ*u))) u := by
  classical
  rcases hF with ⟨L,hLan,hLzero,hbranch⟩
  have hbase := hbranch u hu
  have hL : HasDerivAt L (_root_.deriv L u) u := (hLan u hu).differentiableAt.hasDerivAt
  have hAff : HasDerivAt (fun v : ℂ => ζ+γ*v) γ u := by
    convert ((hasDerivAt_id' u).const_mul γ).const_add ζ using 1 <;> ring
  have hevent : ∀ᶠ v in nhds u, Complex.exp (L v)=jphi (ζ+γ*v)/2 ∧
      F v=(d.c 0:ℂ)*L v-∑ k ∈ Finset.range d.N,
        (d.c (k+1):ℂ)*(jphi (ζ+γ*v))⁻¹^(k+1)/(k+1:ℕ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hu] with v hv
    exact (hbranch v hv).2
  have hExp' : HasDerivAt (fun v : ℂ => jphi (ζ+γ*v)/2)
      (jphi (ζ+γ*u)/jq (ζ+γ*u)*γ/2) u := by
    simpa only [Function.comp_def] using
      ((hasDerivAt_jphi hbase.1).comp u (h:=fun v : ℂ => ζ+γ*v) hAff).div_const 2
  have hder := (hL.cexp.congr_of_eventuallyEq (hevent.mono (fun v hv => hv.1.symm))).unique hExp'
  have hDvalue : _root_.deriv L u=γ/jq (ζ+γ*u) := by
    rw [hbase.2.1] at hder
    apply mul_left_cancel₀ (div_ne_zero (jphi_ne_zero hbase.1) (by norm_num : (2:ℂ)≠0))
    rw [hder]
    ring
  have hL' : HasDerivAt L (γ/jq (ζ+γ*u)) u := by rw [← hDvalue]; exact hL
  have hterm (k : ℕ) : HasDerivAt
      (fun v : ℂ => (d.c (k+1):ℂ)*(jphi (ζ+γ*v))⁻¹^(k+1)/(k+1:ℕ))
      (-(d.c (k+1):ℂ)*(jphi (ζ+γ*u))⁻¹^(k+1)*γ/jq (ζ+γ*u)) u := by
    have hh := (((hasDerivAt_jphi_inv_pow hbase.1 (k+1)).comp u
      (h:=fun v : ℂ => ζ+γ*v) hAff).const_mul (d.c (k+1):ℂ)).div_const (k+1:ℕ)
    simp only [Function.comp_def,← inv_pow] at hh
    convert hh using 1
    field_simp <;> ring
  have hsum : HasDerivAt (fun v : ℂ => ∑ k ∈ Finset.range d.N,
      (d.c (k+1):ℂ)*(jphi (ζ+γ*v))⁻¹^(k+1)/(k+1:ℕ))
      (∑ k ∈ Finset.range d.N, -(d.c (k+1):ℂ)*(jphi (ζ+γ*u))⁻¹^(k+1)*γ/jq (ζ+γ*u)) u :=
    HasDerivAt.fun_sum (fun k _ => hterm k)
  have hfinal := ((hL'.const_mul (d.c 0:ℂ)).sub hsum).congr_of_eventuallyEq
    (hevent.mono (fun v hv => hv.2))
  convert hfinal using 1
  rw [segment_poly_quotient d (ζ+γ*u) hbase.1]
  simp only [div_eq_mul_inv,add_mul,mul_add,Finset.mul_sum,Finset.sum_mul,
    neg_mul,Finset.sum_neg_distrib]
  ring_nf
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem segSeries_coeff (d : SegmentData) (ζ γ : ℂ) (hs : 1 < jc ζ)
    (G : ℂ → ℂ) (hG : IsLocalSegmentPrimitive d ζ G)
    (y f r b : ℕ → ℂ)
    (hy : HasTaylorSeriesAt (fun u => (jq (ζ+γ*u))⁻¹) y 0)
    (hf : HasTaylorSeriesAt (fun u => (fpoly d.c d.N).eval (ζ+γ*u)) f 0)
    (hr : HasTaylorSeriesAt (fun u => (rpoly d.c d.N).eval (ζ+γ*u)) r 0)
    (hb : HasTaylorSeriesAt (fun u => G (ζ+γ*u)) b 0) :
    ∀ n : ℕ, b (n+1)=γ*((∑ i ∈ Finset.range (n+1), f i*y (n-i))-r n)/(n+1:ℕ) := by
  rcases hG with ⟨R,hR,hDisc⟩
  have hcont : Tendsto (fun u : ℂ => γ*u) (nhds 0) (nhds 0) := by
    have hc : Continuous (fun u : ℂ => γ*u) := continuous_const.mul continuous_id'
    simpa using (hc.continuousAt (x:=(0:ℂ))).tendsto
  have hdeq : ∀ᶠ u : ℂ in nhds 0,
      _root_.deriv (fun v => G (ζ+γ*v)) u =
        γ*((fpoly d.c d.N).eval (ζ+γ*u)*(jq (ζ+γ*u))⁻¹-(rpoly d.c d.N).eval (ζ+γ*u)) := by
    filter_upwards [hcont.eventually (Metric.ball_mem_nhds (0:ℂ) hR)] with u hu
    have hpoint := discPrimitive_hasDerivAt d ζ 1 R (fun v => G (ζ+v)) hDisc (γ*u) hu
    simp only [one_mul] at hpoint
    have hscale : HasDerivAt (fun v : ℂ => γ*v) γ u := by
      simpa only [mul_one] using (hasDerivAt_id' u).const_mul γ
    have hG' : HasDerivAt (fun v : ℂ => G (ζ+γ*v))
        (γ*((fpoly d.c d.N).eval (ζ+γ*u)/jq (ζ+γ*u)-(rpoly d.c d.N).eval (ζ+γ*u))) u := by
      convert! hpoint.comp u (h:=fun v : ℂ => γ*v) hscale using 1
      ring
    simpa only [div_eq_mul_inv] using hG'.deriv
  have hc := ((hf.mul hy).sub hr).const_mul γ
  have heq := (hb.deriv.congr hdeq).unique hc
  intro n
  have hh := congrFun heq n
  apply (eq_div_iff (by exact_mod_cast Nat.succ_ne_zero n : ((n+1:ℕ):ℂ)≠0)).2
  linear_combination hh
#print axioms ySeries_rec
#print axioms discPrimitive_hasDerivAt
#print axioms segSeries_coeff
end CatalanCore.Li2.DecayCert
