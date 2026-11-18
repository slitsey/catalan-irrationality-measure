module
public import CatalanCore.Li2.DecayCert.Lattice.Stieltjes.Defs
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Data.Nat.Choose.Central
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Polynomial
open scoped BigOperators
open CatalanCore.Zeta5.Potential
namespace CatalanCore.Li2.DecayCert

theorem centralRatio_step (n : ℕ) :
    (((2*(n+1)).choose (n+1):ℝ)/4^(n+1))=
      ((2*n+1:ℝ)/(2*n+2))*(((2*n).choose n:ℝ)/4^n) := by
  have hc := Nat.succ_mul_centralBinom_succ n
  have hcr : ((n:ℝ)+1)*((2*(n+1)).choose (n+1):ℝ)=
      2*(2*(n:ℝ)+1)*((2*n).choose n:ℝ) := by
    exact_mod_cast hc
  rw [pow_succ]
  field_simp
  nlinarith only [hcr]

theorem arc_cos_power_step (n : ℕ) :
    (∫ θ, Real.cos θ^(n+2) ∂arc)=
      ((n+1:ℝ)/(n+2))*∫ θ, Real.cos θ^n ∂arc := by
  simp_rw [integral_arc,intervalIntegral.integral_const_mul]
  rw [integral_cos_pow]
  simp only [Real.sin_pi,Real.sin_zero,mul_zero,sub_self,zero_div,zero_add]
  ring

theorem arc_cos_even (n : ℕ) :
    (∫ θ, Real.cos θ^(2*n) ∂arc)=((2*n).choose n:ℝ)/4^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega,arc_cos_power_step,ih]
    have h := centralRatio_step n
    rw [show 2*(n+1)=2*n+2 by omega] at h
    push_cast at h ⊢
    exact h.symm

theorem arc_cos_odd (n : ℕ) : (∫ θ, Real.cos θ^(2*n+1) ∂arc)=0 := by
  induction n with
  | zero =>
    have h := integral_T_int (1:ℤ) (by decide)
    simpa only [Chebyshev.T_one,Polynomial.eval_X,pow_one,Nat.mul_zero,Nat.zero_add,zero_mul,zero_add] using h
  | succ n ih =>
    rw [show 2*(n+1)+1=(2*n+1)+2 by omega,arc_cos_power_step,ih,mul_zero]

theorem arc_cos_power (n : ℕ) : (∫ θ, Real.cos θ^n ∂arc)=
    if Even n then (n.choose (n/2):ℝ)/4^(n/2) else 0 := by
  by_cases he : Even n
  · rw [if_pos he]
    rcases he with ⟨k,hk⟩
    have hn : n=2*k := by omega
    rw [hn]
    simpa using arc_cos_even k
  · rw [if_neg he]
    have ho : Odd n := (Nat.even_or_odd n).resolve_left he
    rcases ho with ⟨k,hk⟩
    have hn : n=2*k+1 := by omega
    rw [hn]
    exact arc_cos_odd k

theorem arc_reflection (g : ℝ→ℝ) :
    (∫ θ, g (Real.pi-θ) ∂arc)=∫ θ, g θ ∂arc := by
  rw [integral_arc,integral_arc]
  simpa only [sub_self,sub_zero] using
    intervalIntegral.integral_comp_sub_left (fun θ : ℝ => (1/Real.pi)*g θ) Real.pi (a:=0) (b:=Real.pi)

#print axioms centralRatio_step
#print axioms arc_cos_power
#print axioms arc_reflection
theorem integrable_arc_continuous (f : ℝ→ℝ) (hf : Continuous f) : Integrable f arc := by
  apply (hf.continuousOn.integrableOn_compact isCompact_Icc).integrable_of_ae_notMem_eq_zero
  filter_upwards [CatalanMeasure.Signed.ae_mem_Icc_denMeasure (fun _ => 0) 0] with θ hθ
  intro hn
  exact (hn hθ).elim

theorem arcPolyMoment_integral (p : ℚ[X]) :
    (∫ θ, (p.map (Rat.castHom ℝ)).eval (Real.cos θ) ∂arc)=(arcPolyMoment p:ℝ) := by
  have he (θ : ℝ) : (p.map (Rat.castHom ℝ)).eval (Real.cos θ)=
      ∑ j ∈ Finset.range (p.natDegree+1), (p.coeff j:ℝ)*Real.cos θ^j := by
    rw [Polynomial.eval_map,Polynomial.eval₂_eq_sum_range' (Rat.castHom ℝ) (Nat.lt_succ_self _)]
    rfl
  simp_rw [he]
  rw [integral_finsetSum _ (fun j hj =>
    (integrable_arc_continuous (fun θ => Real.cos θ^j) (by fun_prop)).const_mul (p.coeff j:ℝ))]
  simp_rw [integral_const_mul,arc_cos_power]
  unfold arcPolyMoment
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : Even j <;> simp [h]

theorem positiveArcMoment_integral (ξ : ℚ) (k : ℕ) :
    (∫ θ, ((ξ:ℝ)-Real.cos θ)^k ∂arc)=(positiveArcMoment ξ k:ℝ) := by
  have he : ∀ θ : ℝ,
      ((((Polynomial.C ξ-Polynomial.X)^k).map (Rat.castHom ℝ)).eval (Real.cos θ))=
        ((ξ:ℝ)-Real.cos θ)^k := by
    intro θ
    rw [Polynomial.eval_map]
    simp [Polynomial.eval₂_pow,Polynomial.eval₂_sub,Polynomial.eval₂_C,Polynomial.eval₂_X]
  have h := arcPolyMoment_integral ((Polynomial.C ξ-Polynomial.X)^k)
  simp_rw [he] at h
  simpa only [positiveArcMoment] using h

theorem arc_inverse_moment (φ : ℚ) (hφ : 1<φ) (k : ℕ) :
    (∫ θ, ((((φ+φ⁻¹)/2:ℚ):ℝ)-Real.cos θ)^(-(k:ℤ)) ∂arc)=(momentRec φ k:ℝ) := by
  have h := arcsine_stieltjes_rat φ hφ k
  have hg : Measurable (fun x : ℝ => ((((φ:ℝ)+(φ:ℝ)⁻¹)/2)-x)^(-(k:ℤ))) := by fun_prop
  rw [ωarc,integral_map Real.continuous_cos.aemeasurable hg.aestronglyMeasurable] at h
  simpa only [Rat.cast_div,Rat.cast_add,Rat.cast_inv,Rat.cast_ofNat] using h

theorem arc_shift_power (φ : ℚ) (hφ : 1<φ) (i k : ℕ) :
    (∫ θ, ((((φ+φ⁻¹)/2:ℚ):ℝ)-Real.cos θ)^((i:ℤ)-(k:ℤ)) ∂arc)=
      if i≤k then (momentRec φ (k-i):ℝ) else (positiveArcMoment ((φ+φ⁻¹)/2) (i-k):ℝ) := by
  by_cases hik : i≤k
  · rw [if_pos hik,show (i:ℤ)-(k:ℤ)=-((k-i:ℕ):ℤ) by omega]
    exact arc_inverse_moment φ hφ (k-i)
  · rw [if_neg hik,show (i:ℤ)-(k:ℤ)=((i-k:ℕ):ℤ) by omega]
    simp only [zpow_natCast]
    exact positiveArcMoment_integral _ _

#print axioms arcPolyMoment_integral
#print axioms arc_shift_power
theorem one_lt_joukowski_rat (φ : ℚ) (hφ : 1<φ) : 1<(φ+φ⁻¹)/2 := by
  have hp : 0<φ := lt_trans zero_lt_one hφ
  by_contra h
  have hle : φ+φ⁻¹≤2 := by linarith [le_of_not_gt h]
  have hm := mul_le_mul_of_nonneg_left hle hp.le
  rw [mul_add,mul_inv_cancel₀ hp.ne'] at hm
  nlinarith [sq_pos_of_pos (sub_pos.mpr hφ)]

theorem arc_shift_polynomial (p : ℚ[X]) (φ : ℚ) (hφ : 1<φ) (k : ℕ) :
    (∫ θ, (p.map (Rat.castHom ℝ)).eval ((((φ+φ⁻¹)/2:ℚ):ℝ)-Real.cos θ)*
      (((((φ+φ⁻¹)/2:ℚ):ℝ)-Real.cos θ)^(-(k:ℤ))) ∂arc)=
    ((∑ i ∈ Finset.range (p.natDegree+1),p.coeff i*
      (if i≤k then momentRec φ (k-i) else positiveArcMoment ((φ+φ⁻¹)/2) (i-k)):ℚ):ℝ) := by
  let ξ : ℚ := (φ+φ⁻¹)/2
  have hξ : (1:ℝ)<(ξ:ℝ) := by exact_mod_cast one_lt_joukowski_rat φ hφ
  have hgap (θ : ℝ) : 0<(ξ:ℝ)-Real.cos θ := sub_pos.mpr ((Real.cos_le_one θ).trans_lt hξ)
  have he (θ : ℝ) : (p.map (Rat.castHom ℝ)).eval ((ξ:ℝ)-Real.cos θ)*
      ((ξ:ℝ)-Real.cos θ)^(-(k:ℤ))=
      ∑ i ∈ Finset.range (p.natDegree+1),(p.coeff i:ℝ)*
        ((ξ:ℝ)-Real.cos θ)^((i:ℤ)-(k:ℤ)) := by
    rw [Polynomial.eval_map,Polynomial.eval₂_eq_sum_range' (Rat.castHom ℝ) (Nat.lt_succ_self _),Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc,← zpow_natCast,← zpow_add₀ (hgap θ).ne']
    rfl
  have hi (i : ℕ) : Integrable (fun θ => (p.coeff i:ℝ)*
      ((ξ:ℝ)-Real.cos θ)^((i:ℤ)-(k:ℤ))) arc := by
    apply (integrable_arc_continuous _ ?_).const_mul _
    exact (continuous_const.sub Real.continuous_cos).zpow₀ _ (fun θ => Or.inl (hgap θ).ne')
  change (∫ θ, (p.map (Rat.castHom ℝ)).eval ((ξ:ℝ)-Real.cos θ)*
      ((ξ:ℝ)-Real.cos θ)^(-(k:ℤ)) ∂arc)=_
  simp_rw [he]
  rw [integral_finsetSum _ (fun i hi' => hi i)]
  simp_rw [integral_const_mul]
  have hp (i : ℕ) := arc_shift_power φ hφ i k
  change ∑ i ∈ Finset.range (p.natDegree+1),(p.coeff i:ℝ)*
      (∫ θ, ((ξ:ℝ)-Real.cos θ)^((i:ℤ)-(k:ℤ)) ∂arc)=_
  simp_rw [show ∀ (i : ℕ), (∫ θ, ((ξ:ℝ)-Real.cos θ)^((i:ℤ)-(k:ℤ)) ∂arc)=
      if i≤k then (momentRec φ (k-i):ℝ) else (positiveArcMoment ξ (i-k):ℝ) from hp]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hik : i≤k <;> simp [hik,ξ]

#print axioms arc_shift_polynomial
end CatalanCore.Li2.DecayCert
