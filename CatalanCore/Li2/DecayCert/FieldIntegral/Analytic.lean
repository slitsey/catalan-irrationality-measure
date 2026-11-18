module
public import CatalanCore.Li2.DecayCert.Mass
public import CatalanCore.Tools.JoukowskiLog
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Complex Polynomial Filter Topology
open scoped BigOperators
open CatalanCore.Zeta5.Potential CatalanCore.Tools.Joukowski
namespace CatalanCore.Li2.DecayCert
noncomputable def weightedCheb (d : SegmentData) (a : ℝ) (k : ℕ) : ℂ :=
  let β := d.M+(a:ℂ)
  if k=0 then β*(d.c 0:ℂ)+d.h*(d.c 1:ℂ)/2
  else if k=1 then β*(d.c 1:ℂ)+d.h*(d.c 0:ℂ)+d.h*(d.c 2:ℂ)/2
  else β*(d.c k:ℂ)+d.h*((d.c (k-1):ℂ)+(d.c (k+1):ℂ))/2

inductive FieldIntegralBranch (d : SegmentData) (a : ℝ) : Type
  | leftEnd (h : d.M+(a:ℂ)=d.h) : FieldIntegralBranch d a
  | rightEnd (h : d.M+(a:ℂ)= -d.h) : FieldIntegralBranch d a
  | generic (η : ℂ) (k : ℤ)
      (hη : η= -(d.M+(a:ℂ))/d.h) (hoff : 1 < CatalanCore.Tools.Joukowski.jc η)
      (hline : ∀ᵐ (x : ℝ) ∂ωarc,
        Complex.log (d.M+(a:ℂ)+d.h*(x:ℂ)) =
          Complex.log (-d.h)+Complex.log (η-(x:ℂ))+2*Real.pi*Complex.I*(k:ℂ)) :
      FieldIntegralBranch d a
  | realLine (hM : d.M.im=0) (hh : d.h.im=0)
      (hη : 1 ≤ |(-(d.M+(a:ℂ))/d.h).re|) : FieldIntegralBranch d a
noncomputable def VintFormula (d : SegmentData) (a : ℝ) : FieldIntegralBranch d a → ℝ
  | .leftEnd _ =>
      ((Complex.log d.h-(Real.log 2:ℂ))*weightedCheb d a 0 -
        (∑ k ∈ Finset.range (d.N+1), (-1:ℂ)^(k+1)*weightedCheb d a (k+1)/(k+1:ℕ)) -
          weightedCheb d a 0).re
  | .rightEnd _ =>
      ((Complex.log (-d.h)-(Real.log 2:ℂ))*weightedCheb d a 0 -
        (∑ k ∈ Finset.range (d.N+1), weightedCheb d a (k+1)/(k+1:ℕ)) -
          weightedCheb d a 0).re
  | .generic η k _ _ _ =>
      ((Complex.log (-d.h)+2*Real.pi*Complex.I*(k:ℂ))*weightedCheb d a 0 +
        weightedCheb d a 0*Complex.log (CatalanCore.Tools.Joukowski.jphi η/2) -
        (∑ j ∈ Finset.range (d.N+1), weightedCheb d a (j+1)*(CatalanCore.Tools.Joukowski.jphi η)⁻¹^(j+1)/(j+1:ℕ)) -
          weightedCheb d a 0).re
  | .realLine _ _ _ =>
      let η := -(d.M+(a:ℂ))/d.h
      let ψ := if |η.re|=1 then η else (CatalanCore.Tools.Joukowski.jphi η)⁻¹
      (weightedCheb d a 0).re * (Real.log ‖d.h‖-Real.log 2+
        (if |η.re|=1 then 0 else Real.log ‖CatalanCore.Tools.Joukowski.jphi η‖)) -
      (∑ j ∈ Finset.range (d.N+1), (weightedCheb d a (j+1)*ψ^(j+1)).re/(j+1:ℕ)) -
        (weightedCheb d a 0).re

private noncomputable def wb (β h : ℂ) (j k : ℕ) : ℂ :=
  if k=0 then β*(if j=0 then 1 else 0)+h/2*(if j=1 then 1 else 0)
  else if k=1 then β*(if j=1 then 1 else 0)+h*(if j=0 then 1 else 0)+h/2*(if j=2 then 1 else 0)
  else β*(if j=k then 1 else 0)+h/2*((if j=k-1 then 1 else 0)+(if j=k+1 then 1 else 0))

private theorem wb_column (β h : ℂ) (j k : ℕ) :
    wb β h j k = β*(if k=j then 1 else 0) +
      if j=0 then h*(if k=1 then 1 else 0)
      else h/2*((if k=j+1 then 1 else 0)+(if k=j-1 then 1 else 0)) := by
  unfold wb
  split_ifs <;> (try omega)
  all_goals ring

private theorem finite_c (d : SegmentData) (k : ℕ) :
    (∑ j ∈ Finset.range (d.N+1), if j=k then (d.c j:ℂ) else 0) = (d.c k:ℂ) := by
  rw [Finset.sum_ite_eq']
  split_ifs with hk
  · rfl
  · have hge : d.N < k := by simp only [Finset.mem_range] at hk; omega
    rw [d.finite_coeff k hge]
    simp

private theorem finite_proj (d : SegmentData) (k : ℕ) (A : ℂ) :
    (∑ j ∈ Finset.range (d.N+1), (d.c j:ℂ)*(A*(if j=k then 1 else 0))) = A*(d.c k:ℂ) := by
  have he (j : ℕ) : (d.c j:ℂ)*(A*(if j=k then 1 else 0)) =
      A*(if j=k then (d.c j:ℂ) else 0) := by split_ifs <;> ring
  simp_rw [he]
  rw [← Finset.mul_sum, finite_c]

private theorem wb_coeff (d : SegmentData) (a : ℝ) (k : ℕ) :
    weightedCheb d a k = ∑ j ∈ Finset.range (d.N+1), (d.c j:ℂ)*wb (d.M+(a:ℂ)) d.h j k := by
  unfold weightedCheb wb
  split_ifs <;> simp only [mul_add, Finset.sum_add_distrib] <;> simp_rw [finite_proj] <;> ring

private noncomputable def tv (j : ℕ) (x : ℝ) : ℂ :=
  (((Chebyshev.T ℝ (j:ℤ)).eval x:ℝ):ℂ)
private theorem tv_zero (x : ℝ) : tv 0 x=1 := by simp [tv]
private theorem tv_one (x : ℝ) : tv 1 x=(x:ℂ) := by simp [tv]
private theorem tv_rec (j : ℕ) (x : ℝ) :
    tv (j+2) x=2*(x:ℂ)*tv (j+1) x-tv j x := by
  have he := congrArg (fun p : ℝ[X] => p.eval x) (Chebyshev.T_add_two ℝ (j:ℤ))
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X] at he
  dsimp only [tv]
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  push_cast
  exact_mod_cast he

private theorem wb_eval (d : SegmentData) (a x : ℝ) (j : ℕ) (hj : j ≤ d.N) :
    (∑ k ∈ Finset.range (d.N+2), wb (d.M+(a:ℂ)) d.h j k*tv k x) =
      (d.M+(a:ℂ)+d.h*(x:ℂ))*tv j x := by
  have hj0 : j ∈ Finset.range (d.N+2) := Finset.mem_range.mpr (by omega)
  have hj1 : j+1 ∈ Finset.range (d.N+2) := Finset.mem_range.mpr (by omega)
  have hjm : j-1 ∈ Finset.range (d.N+2) := Finset.mem_range.mpr (by omega)
  by_cases hz : j=0
  · subst j
    simp only [wb_column,ite_true,add_mul,mul_add,mul_ite,ite_mul,one_mul,zero_mul,
      mul_one,mul_zero,Finset.sum_add_distrib,Finset.sum_ite_eq',hj0,hj1,ite_true]
    rw [tv_zero,tv_one]
    ring
  · simp only [wb_column,hz,ite_false,add_mul,mul_add,mul_ite,ite_mul,one_mul,zero_mul,
      mul_one,mul_zero,Finset.sum_add_distrib,Finset.sum_ite_eq',hj0,hj1,hjm,ite_true]
    obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
    simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel]
    rw [show r+1+1=r+2 by omega,tv_rec]
    ring

private theorem weightedCheb_eval (d : SegmentData) (a x : ℝ) :
    (∑ k ∈ Finset.range (d.N+2), weightedCheb d a k*tv k x) =
      (d.M+(a:ℂ)+d.h*(x:ℂ))*(chebF d.c d.N x:ℂ) := by
  have hc : (chebF d.c d.N x:ℂ) = ∑ j ∈ Finset.range (d.N+1), (d.c j:ℂ)*tv j x := by
    unfold chebF tv
    push_cast
    rfl
  rw [hc]
  simp_rw [wb_coeff,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ j ∈ Finset.range (d.N+1), (d.c j:ℂ)*
        ((d.M+(a:ℂ)+d.h*(x:ℂ))*tv j x) := by
      apply Finset.sum_congr rfl
      intro j hj
      have he : (∑ k ∈ Finset.range (d.N+2), ((d.c j:ℂ)*wb (d.M+(a:ℂ)) d.h j k)*tv k x) =
          (d.c j:ℂ)*(∑ k ∈ Finset.range (d.N+2), wb (d.M+(a:ℂ)) d.h j k*tv k x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      rw [he,wb_eval d a x j (by simp only [Finset.mem_range] at hj; omega)]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

private noncomputable def cc (b : ℕ → ℂ) (L : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (L+1), b k*tv k x
private theorem cc_decompose (b : ℕ → ℂ) (L : ℕ) (x : ℝ) :
    cc b L x=(chebF (fun k => (b k).re) L x:ℂ) +
      (chebF (fun k => (b k).im) L x:ℂ)*Complex.I := by
  unfold cc chebF tv
  push_cast
  rw [Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  linear_combination -((Chebyshev.T ℂ (k:ℤ)).eval (x:ℂ))*(Complex.re_add_im (b k))

private theorem cheb_log_integrable (c : ℕ → ℝ) (N : ℕ) {ζ : ℂ} (h : 1 < jc ζ) :
    Integrable (fun θ => (chebF c N (Real.cos θ):ℂ)*Complex.log (ζ-(Real.cos θ:ℂ))) arc := by
  let w := (jphi ζ)⁻¹
  have hw : ‖w‖ < 1 := by dsimp [w]; rw [norm_inv]; exact inv_lt_one_of_one_lt₀ (jphi_spec h).1
  let q : ℝ → ℂ := fun x => 1-2*(x:ℂ)*w+w^2
  have hqc : ContinuousOn q (Icc (-1:ℝ) 1) := by dsimp only [q]; fun_prop
  have hqlog := hqc.clog (fun x hx =>
    CatalanMeasure.GenD.Cert.LogSeriesBand.quad_mem_slitPlane hw (abs_le.mpr hx))
  have hlog : ContinuousOn (fun x : ℝ => Complex.log (ζ-(x:ℂ))) (Icc (-1:ℝ) 1) := by
    have hc : ContinuousOn (fun x : ℝ => Complex.log (jphi ζ/2)+Complex.log (q x)) (Icc (-1:ℝ) 1) :=
      continuousOn_const.add hqlog
    apply hc.congr
    intro x hx
    exact complex_log_jphi h hx
  have hc : ContinuousOn (fun x : ℝ => (chebF c N x:ℂ)*Complex.log (ζ-(x:ℂ))) (Icc (-1:ℝ) 1) :=
    (Complex.continuous_ofReal.comp (continuous_chebF c N)).continuousOn.mul hlog
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact integrable_arc_C (hc.comp_continuous Real.continuous_cos (fun θ => cos_mem θ))
    (fun θ => hC _ (cos_mem θ))

private theorem cc_log_integral (b : ℕ → ℂ) (L : ℕ) {ζ : ℂ} (h : 1 < jc ζ) :
    (∫ θ, cc b L (Real.cos θ)*Complex.log (ζ-(Real.cos θ:ℂ)) ∂arc) =
      b 0*Complex.log (jphi ζ/2)-
        ∑ k ∈ Finset.range L, b (k+1)*(jphi ζ)⁻¹^(k+1)/(k+1:ℕ) := by
  have hiR := cheb_log_integrable (fun k => (b k).re) L h
  have hiI := cheb_log_integrable (fun k => (b k).im) L h
  have hf : (fun θ => cc b L (Real.cos θ)*Complex.log (ζ-(Real.cos θ:ℂ))) =
      fun θ => (chebF (fun k => (b k).re) L (Real.cos θ):ℂ)*Complex.log (ζ-(Real.cos θ:ℂ)) +
        ((chebF (fun k => (b k).im) L (Real.cos θ):ℂ)*Complex.log (ζ-(Real.cos θ:ℂ)))*Complex.I := by
    funext θ
    rw [cc_decompose]
    ring
  rw [hf,integral_add hiR (hiI.mul_const _),integral_mul_const,
    integral_chebF_logC _ _ h,integral_chebF_logC _ _ h]
  have hs : (∑ k ∈ Finset.range L, ((b (k+1)).re:ℂ)*(jphi ζ)⁻¹^(k+1)/(k+1:ℕ)) +
      (∑ k ∈ Finset.range L, ((b (k+1)).im:ℂ)*(jphi ζ)⁻¹^(k+1)/(k+1:ℕ))*Complex.I =
      ∑ k ∈ Finset.range L, b (k+1)*(jphi ζ)⁻¹^(k+1)/(k+1:ℕ) := by
    rw [Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    linear_combination ((jphi ζ)⁻¹^(k+1)/((k+1:ℕ):ℂ))*(Complex.re_add_im (b (k+1)))
  linear_combination Complex.log (jphi ζ/2)*(Complex.re_add_im (b 0))-hs

private theorem cc_real_integral (b : ℕ → ℂ) (L : ℕ) (g : ℝ → ℝ)
    (hR : Integrable (fun θ => chebF (fun k => (b k).re) L (Real.cos θ)*g θ) arc)
    (hI : Integrable (fun θ => chebF (fun k => (b k).im) L (Real.cos θ)*g θ) arc) :
    Integrable (fun θ => cc b L (Real.cos θ)*(g θ:ℂ)) arc ∧
    (∫ θ, cc b L (Real.cos θ)*(g θ:ℂ) ∂arc) =
      ((∫ θ, chebF (fun k => (b k).re) L (Real.cos θ)*g θ ∂arc : ℝ):ℂ) +
      ((∫ θ, chebF (fun k => (b k).im) L (Real.cos θ)*g θ ∂arc : ℝ):ℂ)*Complex.I := by
  have hf : (fun θ => cc b L (Real.cos θ)*(g θ:ℂ)) =
      fun θ => ((chebF (fun k => (b k).re) L (Real.cos θ)*g θ:ℝ):ℂ) +
        ((chebF (fun k => (b k).im) L (Real.cos θ)*g θ:ℝ):ℂ)*Complex.I := by
    funext θ
    rw [cc_decompose]
    push_cast
    ring
  constructor
  · rw [hf]
    exact hR.ofReal.add (hI.ofReal.mul_const _)
  · rw [hf,integral_add hR.ofReal (hI.ofReal.mul_const _),integral_mul_const,
      integral_complex_ofReal,integral_complex_ofReal]

private theorem cc_base (b : ℕ → ℂ) (L : ℕ) :
    Integrable (fun θ => cc b L (Real.cos θ)) arc ∧ (∫ θ, cc b L (Real.cos θ) ∂arc)=b 0 := by
  have hR : Integrable (fun θ => chebF (fun k => (b k).re) L (Real.cos θ)*1) arc :=
    (integrable_chebF _ _).mul_const 1
  have hI : Integrable (fun θ => chebF (fun k => (b k).im) L (Real.cos θ)*1) arc :=
    (integrable_chebF _ _).mul_const 1
  have hh := cc_real_integral b L (fun _ => 1) hR hI
  simpa only [Complex.ofReal_one,mul_one,integral_chebF,Complex.re_add_im] using hh

private theorem cc_log_real (b : ℕ → ℂ) (L : ℕ) (t : ℝ) (ht : t ∈ Icc (-1:ℝ) 1) :
    Integrable (fun θ => cc b L (Real.cos θ)*(Real.log |t-Real.cos θ|:ℂ)) arc ∧
    (∫ θ, cc b L (Real.cos θ)*(Real.log |t-Real.cos θ|:ℂ) ∂arc) =
      -(Real.log 2:ℂ)*b 0-
        ∑ k ∈ Finset.range L, tv (k+1) t*b (k+1)/(k+1:ℕ) := by
  have hR := integral_chebF_log_inside (fun k => (b k).re) L ht
  have hI := integral_chebF_log_inside (fun k => (b k).im) L ht
  have hh := cc_real_integral b L (fun θ => Real.log |t-Real.cos θ|) hR.1 hI.1
  refine ⟨hh.1, ?_⟩
  rw [hh.2,hR.2,hI.2]
  push_cast
  have hs : (∑ k ∈ Finset.range L,
      ((Chebyshev.T ℂ ((k+1:ℕ):ℤ)).eval (t:ℂ))*((b (k+1)).re:ℂ)/(k+1:ℕ)) +
      (∑ k ∈ Finset.range L,
        ((Chebyshev.T ℂ ((k+1:ℕ):ℤ)).eval (t:ℂ))*((b (k+1)).im:ℂ)/(k+1:ℕ))*Complex.I =
      ∑ k ∈ Finset.range L,
        ((Chebyshev.T ℂ ((k+1:ℕ):ℤ)).eval (t:ℂ))*b (k+1)/(k+1:ℕ) := by
    rw [Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    linear_combination (((Chebyshev.T ℂ ((k+1:ℕ):ℤ)).eval (t:ℂ))/((k+1:ℕ):ℂ))*
      (Complex.re_add_im (b (k+1)))
  dsimp only [tv]
  push_cast
  simp only [Nat.cast_add,Nat.cast_one,Int.natCast_add,Int.natCast_one] at hs
  linear_combination -(Real.log 2:ℂ)*(Complex.re_add_im (b 0))-hs

private theorem cc_log_integrable (b : ℕ → ℂ) (L : ℕ) {ζ : ℂ} (h : 1 < jc ζ) :
    Integrable (fun θ => cc b L (Real.cos θ)*Complex.log (ζ-(Real.cos θ:ℂ))) arc := by
  have hiR := cheb_log_integrable (fun k => (b k).re) L h
  have hiI := cheb_log_integrable (fun k => (b k).im) L h
  have hf : (fun θ => cc b L (Real.cos θ)*Complex.log (ζ-(Real.cos θ:ℂ))) =
      fun θ => (chebF (fun k => (b k).re) L (Real.cos θ):ℂ)*Complex.log (ζ-(Real.cos θ:ℂ)) +
        ((chebF (fun k => (b k).im) L (Real.cos θ):ℂ)*Complex.log (ζ-(Real.cos θ:ℂ)))*Complex.I := by
    funext θ
    rw [cc_decompose]
    ring
  rw [hf]
  exact hiR.add (hiI.mul_const _)

private theorem cc_const_log (b : ℕ → ℂ) (L : ℕ) {ζ : ℂ} (h : 1 < jc ζ) (A : ℂ) :
    Integrable (fun θ => cc b L (Real.cos θ)*(A+Complex.log (ζ-(Real.cos θ:ℂ)))) arc ∧
    (∫ θ, cc b L (Real.cos θ)*(A+Complex.log (ζ-(Real.cos θ:ℂ))) ∂arc) =
      A*b 0+b 0*Complex.log (jphi ζ/2)-
        ∑ k ∈ Finset.range L, b (k+1)*(jphi ζ)⁻¹^(k+1)/(k+1:ℕ) := by
  have hbase := cc_base b L
  have hi := cc_log_integrable b L h
  have hf : (fun θ => cc b L (Real.cos θ)*(A+Complex.log (ζ-(Real.cos θ:ℂ)))) =
      fun θ => A*cc b L (Real.cos θ)+cc b L (Real.cos θ)*Complex.log (ζ-(Real.cos θ:ℂ)) := by
    funext θ
    ring
  constructor
  · rw [hf]
    exact (hbase.1.const_mul A).add hi
  · rw [hf,integral_add (hbase.1.const_mul A) hi,integral_const_mul,hbase.2,cc_log_integral b L h]
    ring

private theorem cc_const_log_real (b : ℕ → ℂ) (L : ℕ) (t : ℝ) (ht : t ∈ Icc (-1:ℝ) 1) (A : ℂ) :
    Integrable (fun θ => cc b L (Real.cos θ)*(A+(Real.log |t-Real.cos θ|:ℂ))) arc ∧
    (∫ θ, cc b L (Real.cos θ)*(A+(Real.log |t-Real.cos θ|:ℂ)) ∂arc) =
      A*b 0-(Real.log 2:ℂ)*b 0-
        ∑ k ∈ Finset.range L, tv (k+1) t*b (k+1)/(k+1:ℕ) := by
  have hbase := cc_base b L
  have hi := cc_log_real b L t ht
  have hf : (fun θ => cc b L (Real.cos θ)*(A+(Real.log |t-Real.cos θ|:ℂ))) =
      fun θ => A*cc b L (Real.cos θ)+cc b L (Real.cos θ)*(Real.log |t-Real.cos θ|:ℂ) := by
    funext θ
    ring
  constructor
  · rw [hf]
    exact (hbase.1.const_mul A).add hi.1
  · rw [hf,integral_add (hbase.1.const_mul A) hi.1,integral_const_mul,hbase.2,hi.2]
    ring

private theorem Vint_from_angle (d : SegmentData) (hpos : d.densityNonneg) (a : ℝ)
    (l : ℝ → ℂ)
    (hl : ∀ᵐ θ ∂arc,
      (cc (weightedCheb d a) (d.N+1) (Real.cos θ)*
        Complex.log (d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ))).re =
      (cc (weightedCheb d a) (d.N+1) (Real.cos θ)*l θ).re)
    (hi : Integrable (fun θ => cc (weightedCheb d a) (d.N+1) (Real.cos θ)*l θ) arc) :
    Integrable (fun s => ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re) d.ν ∧
    (∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.ν) =
      ((∫ θ, cc (weightedCheb d a) (d.N+1) (Real.cos θ)*l θ ∂arc)-weightedCheb d a 0).re := by
  let g : ℂ → ℝ := fun s => ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re
  have hg : Measurable g := by dsimp only [g]; fun_prop
  have hcc := cc_base (weightedCheb d a) (d.N+1)
  have hid (θ : ℝ) : cc (weightedCheb d a) (d.N+1) (Real.cos θ) =
      (d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ))*(chebF d.c d.N (Real.cos θ):ℂ) := by
    exact weightedCheb_eval d a (Real.cos θ)
  have hpoint (θ : ℝ) : chebF d.c d.N (Real.cos θ)*g (d.M+d.h*(Real.cos θ:ℂ)) =
      (cc (weightedCheb d a) (d.N+1) (Real.cos θ)*
        Complex.log (d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ)) -
        cc (weightedCheb d a) (d.N+1) (Real.cos θ)).re := by
    have harg : (d.M+d.h*(Real.cos θ:ℂ))+(a:ℂ)=d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ) := by ring
    have he : (chebF d.c d.N (Real.cos θ):ℂ)*
        (((d.M+d.h*(Real.cos θ:ℂ))+(a:ℂ))*Complex.log ((d.M+d.h*(Real.cos θ:ℂ))+(a:ℂ)) -
          ((d.M+d.h*(Real.cos θ:ℂ))+(a:ℂ))) =
        cc (weightedCheb d a) (d.N+1) (Real.cos θ)*
          Complex.log (d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ)) -
          cc (weightedCheb d a) (d.N+1) (Real.cos θ) := by
      rw [harg,hid]
      ring
    have hr := congrArg Complex.re he
    simpa only [g,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hr
  have hae : (fun θ => chebF d.c d.N (Real.cos θ)*g (d.M+d.h*(Real.cos θ:ℂ))) =ᵐ[arc]
      (fun θ => (cc (weightedCheb d a) (d.N+1) (Real.cos θ)*l θ -
        cc (weightedCheb d a) (d.N+1) (Real.cos θ)).re) := by
    filter_upwards [hl] with θ hθ
    rw [hpoint,Complex.sub_re,hθ,← Complex.sub_re]
  have hif : Integrable (fun θ => cc (weightedCheb d a) (d.N+1) (Real.cos θ)*l θ -
      cc (weightedCheb d a) (d.N+1) (Real.cos θ)) arc := hi.sub hcc.1
  have hir : Integrable (fun θ => (cc (weightedCheb d a) (d.N+1) (Real.cos θ)*l θ -
      cc (weightedCheb d a) (d.N+1) (Real.cos θ)).re) arc := by
    simpa only [RCLike.re_to_complex] using hif.re
  have hir' := hir.congr hae.symm
  refine ⟨?_, ?_⟩
  · exact (CatalanCore.Lai.DecayEnergy.integrable_segMeasure_iff (M := d.M) (h := d.h) hpos hg).mpr hir'
  · change (∫ s, g s ∂d.ν)=_
    rw [show d.ν=segMeasure d.M d.h d.c d.N from rfl,integral_segMeasure hpos hg,
      integral_congr_ae hae]
    have hre := integral_re hif
    simp only [RCLike.re_to_complex] at hre
    rw [hre]
    have hs := integral_sub (μ := arc)
      (f := fun θ => cc (weightedCheb d a) (d.N+1) (Real.cos θ)*l θ)
      (g := fun θ => cc (weightedCheb d a) (d.N+1) (Real.cos θ)) hi hcc.1
    rw [hs,hcc.2]

private theorem Vint_generic (d : SegmentData) (hpos : d.densityNonneg) (a : ℝ)
    (η : ℂ) (k : ℤ) (hη : η= -(d.M+(a:ℂ))/d.h) (hoff : 1 < jc η)
    (hline : ∀ᵐ (x : ℝ) ∂ωarc,
      Complex.log (d.M+(a:ℂ)+d.h*(x:ℂ)) =
        Complex.log (-d.h)+Complex.log (η-(x:ℂ))+2*Real.pi*Complex.I*(k:ℂ)) :
    (∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.ν) =
      VintFormula d a (.generic η k hη hoff hline) := by
  let A : ℂ := Complex.log (-d.h)+2*Real.pi*Complex.I*(k:ℂ)
  have hi := cc_const_log (weightedCheb d a) (d.N+1) hoff A
  have hp : ∀ᵐ θ ∂arc,
      Complex.log (d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ)) =
        Complex.log (-d.h)+Complex.log (η-(Real.cos θ:ℂ))+2*Real.pi*Complex.I*(k:ℂ) :=
    ae_of_ae_map Real.continuous_cos.aemeasurable hline
  have hl : ∀ᵐ θ ∂arc,
      (cc (weightedCheb d a) (d.N+1) (Real.cos θ)*
        Complex.log (d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ))).re =
      (cc (weightedCheb d a) (d.N+1) (Real.cos θ)*
        (A+Complex.log (η-(Real.cos θ:ℂ)))).re := by
    filter_upwards [hp] with θ hθ
    rw [hθ]
    congr 1
    dsimp [A]
    ring
  have hv := Vint_from_angle d hpos a _ hl hi.1
  rw [hv.2,hi.2]
  rfl

private theorem Vint_endpoint (d : SegmentData) (hpos : d.densityNonneg) (a : ℝ)
    (t : ℝ) (ht : t ∈ Icc (-1:ℝ) 1) (H : ℂ) (hH : H ≠ 0)
    (hfac : ∀ θ : ℝ, d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ)=H*((|t-Real.cos θ|:ℝ):ℂ)) :
    (∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.ν) =
      ((Complex.log H-(Real.log 2:ℂ))*weightedCheb d a 0 -
        (∑ j ∈ Finset.range (d.N+1), tv (j+1) t*weightedCheb d a (j+1)/(j+1:ℕ)) -
        weightedCheb d a 0).re := by
  have hi := cc_const_log_real (weightedCheb d a) (d.N+1) t ht (Complex.log H)
  have hl : ∀ᵐ θ ∂arc,
      (cc (weightedCheb d a) (d.N+1) (Real.cos θ)*
        Complex.log (d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ))).re =
      (cc (weightedCheb d a) (d.N+1) (Real.cos θ)*
        (Complex.log H+(Real.log |t-Real.cos θ|:ℂ))).re := by
    filter_upwards [ae_cos_ne t ht] with θ hθ
    have hp : 0 < |t-Real.cos θ| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hθ))
    rw [hfac θ,Complex.log_mul_ofReal _ hp H hH]
    congr 1
    ring
  have hv := Vint_from_angle d hpos a _ hl hi.1
  rw [hv.2,hi.2]
  congr 1
  ring

private theorem Vint_leftEnd (d : SegmentData) (hpos : d.densityNonneg) (a : ℝ)
    (hβ : d.M+(a:ℂ)=d.h) :
    (∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.ν) =
      VintFormula d a (.leftEnd hβ) := by
  have hfac (θ : ℝ) : d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ)=d.h*((|(-1:ℝ)-Real.cos θ|:ℝ):ℂ) := by
    rw [hβ,abs_of_nonpos (by linarith [Real.neg_one_le_cos θ])]
    push_cast
    ring
  have hv := Vint_endpoint d hpos a (-1) (by constructor <;> norm_num) d.h d.h_ne hfac
  rw [hv]
  unfold VintFormula
  congr 3
  apply Finset.sum_congr rfl
  intro j hj
  have hjcast : ((j:ℤ)+1).natAbs=j+1 := by omega
  simp [tv,hjcast]

private theorem Vint_rightEnd (d : SegmentData) (hpos : d.densityNonneg) (a : ℝ)
    (hβ : d.M+(a:ℂ)= -d.h) :
    (∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.ν) =
      VintFormula d a (.rightEnd hβ) := by
  have hfac (θ : ℝ) : d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ)=(-d.h)*((|(1:ℝ)-Real.cos θ|:ℝ):ℂ) := by
    rw [hβ,abs_of_nonneg (by linarith [Real.cos_le_one θ])]
    push_cast
    ring
  have hv := Vint_endpoint d hpos a 1 (by constructor <;> norm_num) (-d.h) (neg_ne_zero.mpr d.h_ne) hfac
  rw [hv]
  unfold VintFormula
  congr 3
  apply Finset.sum_congr rfl
  intro j hj
  simp [tv]

private theorem weightedCheb_im_real (d : SegmentData) (a : ℝ)
    (hM : d.M.im=0) (hh : d.h.im=0) (k : ℕ) : (weightedCheb d a k).im=0 := by
  unfold weightedCheb
  split_ifs <;> simp [Complex.mul_im,hM,hh]

private theorem cc_im_real (d : SegmentData) (a : ℝ)
    (hM : d.M.im=0) (hh : d.h.im=0) (x : ℝ) :
    (cc (weightedCheb d a) (d.N+1) x).im=0 := by
  change (∑ k ∈ Finset.range (d.N+2), weightedCheb d a k*tv k x).im=0
  rw [weightedCheb_eval]
  simp [Complex.mul_im,hM,hh]

private theorem Vint_real_off (d : SegmentData) (hpos : d.densityNonneg) (a : ℝ)
    (hM : d.M.im=0) (hh : d.h.im=0) (hoff : 1 < jc (-(d.M+(a:ℂ))/d.h)) :
    (∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.ν) =
      (weightedCheb d a 0).re*(Real.log ‖d.h‖-Real.log 2+
        Real.log ‖jphi (-(d.M+(a:ℂ))/d.h)‖) -
      (∑ j ∈ Finset.range (d.N+1),
        (weightedCheb d a (j+1)*(jphi (-(d.M+(a:ℂ))/d.h))⁻¹^(j+1)).re/(j+1:ℕ)) -
      (weightedCheb d a 0).re := by
  let η : ℂ := -(d.M+(a:ℂ))/d.h
  have hη : 1 < jc η := hoff
  have hi := cc_const_log (weightedCheb d a) (d.N+1) hη (Real.log ‖d.h‖:ℂ)
  have hfac (θ : ℝ) : d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ)=(-d.h)*(η-(Real.cos θ:ℂ)) := by
    dsimp only [η]
    field_simp [d.h_ne]
    <;> ring
  have hl : ∀ᵐ θ ∂arc,
      (cc (weightedCheb d a) (d.N+1) (Real.cos θ)*
        Complex.log (d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ))).re =
      (cc (weightedCheb d a) (d.N+1) (Real.cos θ)*
        ((Real.log ‖d.h‖:ℂ)+Complex.log (η-(Real.cos θ:ℂ)))).re := by
    filter_upwards [] with θ
    have hx : Real.cos θ ∈ Icc (-1:ℝ) 1 := ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩
    have hne : η-(Real.cos θ:ℂ) ≠ 0 := by
      intro hz
      have he : η=(Real.cos θ:ℂ) := sub_eq_zero.mp hz
      have hc := jc_ofReal hx
      rw [he,hc] at hη
      linarith
    simp only [Complex.mul_re,cc_im_real d a hM hh,zero_mul,sub_zero,
      Complex.add_re,Complex.ofReal_re,Complex.log_re]
    rw [hfac,norm_mul,norm_neg,Real.log_mul (norm_ne_zero_iff.mpr d.h_ne) (norm_ne_zero_iff.mpr hne)]
  have hv := Vint_from_angle d hpos a _ hl hi.1
  rw [hv.2,hi.2]
  have hn : Real.log ‖jphi η/2‖=Real.log ‖jphi η‖-Real.log 2 := by
    rw [norm_div,Real.log_div (norm_ne_zero_iff.mpr (jphi_ne_zero hη)) (by norm_num)]
    norm_num
  simp only [Complex.sub_re,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    weightedCheb_im_real d a hM hh,zero_mul,mul_zero,sub_zero,Complex.log_re,
    Complex.re_sum,Complex.div_natCast_re,hn]
  ring

private theorem Vint_real_boundary (d : SegmentData) (hpos : d.densityNonneg) (a : ℝ)
    (hM : d.M.im=0) (hh : d.h.im=0) (habs : |(-(d.M+(a:ℂ))/d.h).re|=1) :
    (∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.ν) =
      (weightedCheb d a 0).re*(Real.log ‖d.h‖-Real.log 2) -
      (∑ j ∈ Finset.range (d.N+1),
        (weightedCheb d a (j+1)*(-(d.M+(a:ℂ))/d.h)^(j+1)).re/(j+1:ℕ)) -
      (weightedCheb d a 0).re := by
  let η : ℂ := -(d.M+(a:ℂ))/d.h
  have hηabs : |η.re|=1 := habs
  have hηim : η.im=0 := by simp [η,Complex.div_im,Complex.mul_im,hM,hh]
  have hηreal : η=(η.re:ℂ) := by apply Complex.ext <;> simp [hηim]
  have ht : η.re ∈ Icc (-1:ℝ) 1 := abs_le.mp hηabs.le
  have hi := cc_const_log_real (weightedCheb d a) (d.N+1) η.re ht (Real.log ‖d.h‖:ℂ)
  have hfac (θ : ℝ) : d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ)=(-d.h)*(η-(Real.cos θ:ℂ)) := by
    dsimp only [η]
    field_simp [d.h_ne] <;> ring
  have hl : ∀ᵐ θ ∂arc,
      (cc (weightedCheb d a) (d.N+1) (Real.cos θ)*
        Complex.log (d.M+(a:ℂ)+d.h*(Real.cos θ:ℂ))).re =
      (cc (weightedCheb d a) (d.N+1) (Real.cos θ)*
        ((Real.log ‖d.h‖:ℂ)+(Real.log |η.re-Real.cos θ|:ℂ))).re := by
    filter_upwards [ae_cos_ne η.re ht] with θ hθ
    have hne : η.re-Real.cos θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
    have hn : ‖η-(Real.cos θ:ℂ)‖=|η.re-Real.cos θ| := by
      rw [hηreal,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      simp only [Complex.ofReal_re]
    simp only [Complex.mul_re,cc_im_real d a hM hh,zero_mul,sub_zero,
      Complex.add_re,Complex.ofReal_re,Complex.log_re]
    rw [hfac,norm_mul,norm_neg,hn,Real.log_mul (norm_ne_zero_iff.mpr d.h_ne) (abs_ne_zero.mpr hne)]
  have hv := Vint_from_angle d hpos a _ hl hi.1
  have htv (n : ℕ) : tv n η.re=η^n := by
    by_cases hp : 0 ≤ η.re
    · have he : η.re=1 := by rwa [abs_of_nonneg hp] at hηabs
      rw [hηreal,he]
      simp [tv]
    · have he : η.re= -1 := by rw [abs_of_nonpos (le_of_not_ge hp)] at hηabs; linarith
      rw [hηreal,he]
      simp [tv]
  rw [hv.2,hi.2]
  simp only [htv]
  have hsum : (∑ j ∈ Finset.range (d.N+1), η^(j+1)*weightedCheb d a (j+1)/(j+1:ℕ)) =
      ∑ j ∈ Finset.range (d.N+1), weightedCheb d a (j+1)*η^(j+1)/(j+1:ℕ) := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.re_sum,Complex.div_natCast_re]
  ring

private theorem Vint_realLine (d : SegmentData) (hpos : d.densityNonneg) (a : ℝ)
    (hM : d.M.im=0) (hh : d.h.im=0) (hη : 1 ≤ |(-(d.M+(a:ℂ))/d.h).re|) :
    (∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.ν) =
      VintFormula d a (.realLine hM hh hη) := by
  by_cases hb : |(-(d.M+(a:ℂ))/d.h).re|=1
  · simpa only [VintFormula,hb,ite_true,add_zero] using Vint_real_boundary d hpos a hM hh hb
  · have hoff : 1 < jc (-(d.M+(a:ℂ))/d.h) := by
      let η : ℂ := -(d.M+(a:ℂ))/d.h
      have him : η.im=0 := by simp [η,Complex.div_im,Complex.mul_im,hM,hh]
      have hre : η=(η.re:ℂ) := by apply Complex.ext <;> simp [him]
      have hab : 1 < |η.re| := lt_of_le_of_ne hη (Ne.symm hb)
      change 1 < jc η
      rw [hre]
      unfold jc
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,← Complex.ofReal_add,
        Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
      by_cases hp : 0 ≤ η.re
      · rw [abs_of_nonneg hp] at hab
        rw [abs_of_pos (by linarith),abs_of_pos (by linarith)]
        linarith
      · rw [abs_of_neg (lt_of_not_ge hp)] at hab
        rw [abs_of_neg (by linarith),abs_of_neg (by linarith)]
        linarith
    simpa only [VintFormula,hb,ite_false] using Vint_real_off d hpos a hM hh hoff

theorem Vint_closed (d : SegmentData) (hpos : d.densityNonneg) (a : ℝ)
    (br : FieldIntegralBranch d a) :
    (∫ s, ((s+(a:ℂ))*Complex.log (s+(a:ℂ))-(s+(a:ℂ))).re ∂d.ν) = VintFormula d a br := by
  cases br with
  | leftEnd h => exact Vint_leftEnd d hpos a h
  | rightEnd h => exact Vint_rightEnd d hpos a h
  | generic η k hη hoff hline => exact Vint_generic d hpos a η k hη hoff hline
  | realLine hM hh hη => exact Vint_realLine d hpos a hM hh hη

#print axioms Vint_realLine
#print axioms Vint_closed

#print axioms Vint_real_boundary

#print axioms weightedCheb_im_real
#print axioms cc_im_real
#print axioms Vint_real_off

#print axioms Vint_endpoint
#print axioms Vint_leftEnd
#print axioms Vint_rightEnd

#print axioms Vint_generic

#print axioms cc_log_integrable
#print axioms cc_const_log
#print axioms cc_const_log_real
#print axioms Vint_from_angle
#print axioms cc_real_integral
#print axioms cc_base
#print axioms cc_log_real
#print axioms weightedCheb_eval
#print axioms cc_decompose
#print axioms cheb_log_integrable
#print axioms cc_log_integral
#print axioms wb_column
#print axioms wb_coeff
#print axioms tv_rec
#print axioms wb_eval
end CatalanCore.Li2.DecayCert
