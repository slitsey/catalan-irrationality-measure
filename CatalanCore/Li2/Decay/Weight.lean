module
public import CatalanCore.Li2.Decay.Fields
public import CatalanCore.Decay.LemmaW
@[expose] public section
/-! LD08: literal weight and monotone logarithmic product bound. Reuses built sum-integral comparison. -/
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace CatalanCore.Li2.Decay
noncomputable def Dprod (m : ℕ) (u : ℂ) : ℂ := ∏ i ∈ Finset.Icc 1 m, (u+(i:ℂ))
noncomputable def weight (n : ℕ) (u : ℂ) : ℂ := Dprod n u^3/Dprod (4*n) u
noncomputable def weightMajorant (z : ℝ) (n : ℕ) (C : ℝ) (u : ℂ) : ℝ :=
  C*(n:ℝ)^C*(1+‖u/(n:ℂ)‖)^C*Real.exp ((n:ℝ)*(V z (u/(n:ℂ))-Real.log n))
theorem Dprod_eq_range (m : ℕ) (u : ℂ) :
    Dprod m u = ∏ j ∈ Finset.range m, (u+((j+1:ℕ):ℂ)) := by
  induction m with
  | zero => simp [Dprod]
  | succ m ih =>
    change (∏ j ∈ Finset.Icc 1 (m+1), (u+(j:ℂ))) = _
    rw [Finset.prod_Icc_succ_top (by omega)]
    change Dprod m u*(u+((m+1:ℕ):ℂ)) = _
    rw [ih,Finset.prod_range_succ]
theorem norm_add_mono (u : ℂ) (hre : 0 ≤ u.re) :
    MonotoneOn (fun x : ℝ => ‖u+(x:ℂ)‖) (Ici 0) := by
  intro x hx y hy hxy
  apply CatalanCore.Decay.LemmaW.le_of_sq' (norm_nonneg _) (norm_nonneg _)
  rw [CatalanCore.Decay.LemmaW.norm_add_ofReal_sq,CatalanCore.Decay.LemmaW.norm_add_ofReal_sq]
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  nlinarith
theorem norm_le_norm_add (u : ℂ) (hre : 0 ≤ u.re) (x : ℝ) (hx : 0 ≤ x) :
    ‖u‖ ≤ ‖u+(x:ℂ)‖ := by
  simpa only [Complex.ofReal_zero,add_zero] using norm_add_mono u hre (show (0:ℝ) ∈ Ici 0 from le_rfl) hx hx
theorem log_add_mono (u : ℂ) (hre : 0 ≤ u.re) (hu : 0 < ‖u‖) :
    MonotoneOn (fun x : ℝ => Real.log ‖u+(x:ℂ)‖) (Ici 0) := by
  intro x hx y hy hxy
  apply Real.log_le_log
  · exact hu.trans_le (norm_le_norm_add u hre x hx)
  · exact norm_add_mono u hre hx hy hxy
theorem Dprod_log (m : ℕ) (u : ℂ) (hre : 0 ≤ u.re) (hu : 0 < ‖u‖) :
    Real.log ‖Dprod m u‖ = ∑ j ∈ Finset.range m, Real.log ‖u+((j+1:ℕ):ℂ)‖ := by
  rw [Dprod_eq_range,norm_prod]
  apply Real.log_prod
  intro j hj
  exact (hu.trans_le (norm_le_norm_add u hre (j+1:ℕ) (by positivity))).ne'
theorem weight_log_eq (n : ℕ) (u : ℂ) (hre : 0 ≤ u.re) (hu : 0 < ‖u‖) :
    Real.log ‖weight n u‖ =
      3*(∑ j ∈ Finset.range n, Real.log ‖u+((j+1:ℕ):ℂ)‖) -
        ∑ j ∈ Finset.range (4*n), Real.log ‖u+((j+1:ℕ):ℂ)‖ := by
  have hd (m : ℕ) : Dprod m u ≠ 0 := by
    rw [Dprod_eq_range]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact norm_ne_zero_iff.mp (hu.trans_le (norm_le_norm_add u hre (j+1:ℕ) (by positivity))).ne'
  rw [weight,norm_div,norm_pow,Real.log_div (pow_ne_zero 3 (norm_ne_zero_iff.mpr (hd n)))
    (norm_ne_zero_iff.mpr (hd (4*n))),Real.log_pow,Dprod_log n u hre hu,Dprod_log (4*n) u hre hu]
  norm_num
theorem right_sum_bounds (u : ℂ) (hre : 0 ≤ u.re) (hu : 0 < ‖u‖) (m : ℕ) :
    (∫ x in (0:ℝ)..(m:ℝ), Real.log ‖u+(x:ℂ)‖) ≤
      (∑ j ∈ Finset.range m, Real.log ‖u+((j+1:ℕ):ℂ)‖) ∧
    (∑ j ∈ Finset.range m, Real.log ‖u+((j+1:ℕ):ℂ)‖) ≤
      (∫ x in (0:ℝ)..(m:ℝ), Real.log ‖u+(x:ℂ)‖) + Real.log ‖u+(m:ℂ)‖-Real.log ‖u‖ := by
  have hm : MonotoneOn (fun x : ℝ => Real.log ‖u+(x:ℂ)‖) (Icc 0 (0+(m:ℝ))) :=
    (log_add_mono u hre hu).mono (fun x hx => hx.1)
  have hlow := hm.integral_le_sum
  have hupp := hm.sum_le_integral
  simp only [zero_add,Complex.ofReal_natCast] at hlow hupp
  have he := Finset.sum_range_succ' (fun j : ℕ => Real.log ‖u+(j:ℂ)‖) m
  rw [Finset.sum_range_succ] at he
  simp only [Nat.cast_zero,add_zero] at he
  exact ⟨hlow,by linarith⟩

theorem integral_log_add_scale (u : ℂ) (hre : 0 ≤ u.re) (hu : 0 < ‖u‖)
    (n B : ℝ) (hn : 0 < n) (hB : 0 ≤ B) :
    (∫ x in (0:ℝ)..(B*n), Real.log ‖u+(x:ℂ)‖) =
      n*(B*Real.log n+(∫ y in (0:ℝ)..B, Real.log ‖u/(n:ℂ)+(y:ℂ)‖)) := by
  let G := fun y : ℝ => Real.log n+Real.log ‖u/(n:ℂ)+(y:ℂ)‖
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hre' : 0 ≤ (u/(n:ℂ)).re := by rw [Complex.div_ofReal_re]; exact div_nonneg hre hn.le
  have hu' : 0 < ‖u/(n:ℂ)‖ := norm_pos_iff.mpr (div_ne_zero (norm_pos_iff.mp hu) hnC)
  have hpt (x : ℝ) (hx : 0 ≤ x) : Real.log ‖u+(x:ℂ)‖ = G (x/n) := by
    have he : u+(x:ℂ) = (n:ℂ)*(u/(n:ℂ)+((x/n:ℝ):ℂ)) := by
      push_cast
      field_simp
    have hnorm : 0 < ‖u/(n:ℂ)+((x/n:ℝ):ℂ)‖ :=
      hu'.trans_le (norm_le_norm_add _ hre' _ (div_nonneg hx hn.le))
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn,
      Real.log_mul hn.ne' hnorm.ne']
  calc
    (∫ x in (0:ℝ)..(B*n), Real.log ‖u+(x:ℂ)‖) = ∫ x in (0:ℝ)..(B*n), G (x/n) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (mul_nonneg hB hn.le)] at hx
      exact hpt x hx.1
    _ = n*(∫ y in (0:ℝ)..B, G y) := by
      rw [intervalIntegral.integral_comp_div G hn.ne']
      simp only [zero_div,mul_div_cancel_right₀ _ hn.ne',smul_eq_mul]
    _ = n*(B*Real.log n+(∫ y in (0:ℝ)..B, Real.log ‖u/(n:ℂ)+(y:ℂ)‖)) := by
      have hc : ContinuousOn (fun y : ℝ => Real.log ‖u/(n:ℂ)+(y:ℂ)‖) (uIcc 0 B) := by
        apply ContinuousOn.log (by fun_prop)
        intro y hy
        rw [uIcc_of_le hB] at hy
        exact (hu'.trans_le (norm_le_norm_add _ hre' _ hy.1)).ne'
      rw [intervalIntegral.integral_add (intervalIntegrable_const (c := Real.log n)) hc.intervalIntegrable]
      simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]

theorem weight_log_le (n : ℕ) (hn : 0 < n) (u : ℂ)
    (hre : 0 ≤ u.re) (hu : 1/2 ≤ ‖u‖) :
    Real.log ‖weight n u‖ ≤ (n:ℝ)*phi0 (u/n)-n*Real.log n+
      3*Real.log (‖u‖+n+1)+3*Real.log 2 := by
  have hu0 : 0 < ‖u‖ := by linarith
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnum := (right_sum_bounds u hre hu0 n).2
  have hden := (right_sum_bounds u hre hu0 (4*n)).1
  have hscale1 := integral_log_add_scale u hre hu0 (n:ℝ) 1 hnR (by norm_num)
  have hscale4 := integral_log_add_scale u hre hu0 (n:ℝ) 4 hnR (by norm_num)
  simp only [one_mul] at hscale1
  have hhead : Real.log ‖u+(n:ℂ)‖ ≤ Real.log (‖u‖+(n:ℝ)+1) := by
    apply Real.log_le_log
    · exact hu0.trans_le (norm_le_norm_add u hre n (Nat.cast_nonneg n))
    · have hh := norm_add_le u (n:ℂ)
      simp only [Complex.norm_natCast] at hh
      linarith
  have hbase : -Real.log ‖u‖ ≤ Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ) < 1/2) hu
    rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),Real.log_one,zero_sub] at hh
    linarith
  rw [weight_log_eq n u hre hu0]
  change _ ≤ (n:ℝ)*(3*(∫ y in (0:ℝ)..1, Real.log ‖u/(n:ℂ)+(y:ℂ)‖)-
    (∫ y in (0:ℝ)..4, Real.log ‖u/(n:ℂ)+(y:ℂ)‖))-(n:ℝ)*Real.log n+
    3*Real.log (‖u‖+(n:ℝ)+1)+3*Real.log 2
  have he : ((4*n:ℕ):ℝ) = 4*(n:ℝ) := by push_cast; ring
  rw [he] at hden
  rw [hscale1] at hnum
  rw [hscale4] at hden
  simp only [Complex.ofReal_natCast] at hnum hden
  nlinarith

end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.weight_log_eq
#print axioms CatalanCore.Li2.Decay.right_sum_bounds

#print axioms CatalanCore.Li2.Decay.weight_log_le
