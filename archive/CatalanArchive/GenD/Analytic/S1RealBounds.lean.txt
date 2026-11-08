module
public import CatalanMeasure.GenD.Analytic.S1BlockBounds
@[expose] public section
namespace CatalanMeasure.GenD.Analytic
noncomputable section

theorem ellipseH_le_norm_add_one (v : ℂ) : ellipseH v ≤ ‖v‖+1 := by
  have hm := norm_sub_le v (1 : ℂ)
  have hp := norm_add_le v (1 : ℂ)
  rw [norm_one] at hm hp
  unfold ellipseH
  linarith

theorem real_segment_weight_le_of_power (v : ℂ) {x H R E C B : ℝ}
    (hx : |x| ≤ 1) (hv : ‖v‖ ≤ B) (hBH : B+1 ≤ H)
    (hHR : H ≤ R) (hsq : H^2-1 ≤ (R-H)^2)
    (hpower : R^33*(4 : ℝ)^260*5^780 ≤ E*3^780)
    (hE : E ≤ Real.exp (65*C)) :
    (66 : ℝ)/130*ellipseLog v+8*Real.log ‖(1 : ℂ)-(x : ℂ)‖ ≤
      C+12*Real.log (3/5) := by
  have h5 : (0 : ℝ) < 5^780 := by positivity
  have hp : R^33*(4 : ℝ)^260 ≤ E*(3/5 : ℝ)^780 := by
    have hh := (le_div_iff₀ h5).mpr hpower
    convert hh using 1 <;> rw [div_pow] <;> ring
  have hexp : Real.exp (65*(C+12*Real.log (3/5))) =
      Real.exp (65*C)*(3/5 : ℝ)^780 := by
    rw [show 65*(C+12*Real.log (3/5 : ℝ)) =
        65*C+(780 : ℕ)*Real.log (3/5) by norm_num; ring,
      Real.exp_add,Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 3/5)]
  have hp' : R^33*(4 : ℝ)^260 ≤ Real.exp (65*(C+12*Real.log (3/5))) := by
    rw [hexp]
    exact hp.trans (mul_le_mul_of_nonneg_right hE (by positivity))
  have hn : ‖(1 : ℂ)-(x : ℂ)‖ ≤ 2 := by
    have hh := norm_sub_le (1 : ℂ) (x : ℂ)
    rw [norm_one] at hh
    simpa only [norm_one,Complex.norm_real,Real.norm_eq_abs] using
      hh.trans (show 1+‖(x : ℂ)‖ ≤ 2 by rw [Complex.norm_real,Real.norm_eq_abs]; linarith)
  have hH : ellipseH v ≤ H := (ellipseH_le_norm_add_one v).trans (by linarith)
  by_cases hzero : ‖(1 : ℂ)-(x : ℂ)‖=0
  · have hR : 0 < R := by have hh := ellipseH_ge_one v; linarith
    have hpure : R^33 ≤ Real.exp (65*(C+12*Real.log (3/5))) := by
      apply le_trans (b := R^33*(4 : ℝ)^260) _ hp'
      calc
        R^33 = R^33*1 := by ring
        _ ≤ R^33*(4 : ℝ)^260 := mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)) (pow_nonneg hR.le _)
    have hlog := Real.log_le_log (pow_pos hR 33) hpure
    rw [Real.log_pow,Real.log_exp] at hlog
    norm_num only [Nat.cast_ofNat] at hlog
    have hg := ellipseLog_le_log_of_square hH hHR hsq
    rw [hzero,Real.log_zero]
    linarith
  · exact circle_weight_le_of_power hH hHR hsq hzero
      (by nlinarith [norm_nonneg ((1 : ℂ)-(x : ℂ))]) hp'

theorem real_segment_phi_of_strong {κ x C G : ℝ} (hκ : 0 ≤ κ)
    (hx0 : (3/5 : ℝ) ≤ |x|) (hx1 : |x| ≤ 1)
    (hG : G ≤ C+12*Real.log (3/5)) :
    (12-72*κ)*Real.log |x|+G ≤ (12-72*κ)*Real.log (3/5)+C := by
  have hx : 0 < |x| := lt_of_lt_of_le (by norm_num) hx0
  have hlo : Real.log (3/5) ≤ Real.log |x| := Real.log_le_log (by norm_num) hx0
  have hhi : Real.log |x| ≤ 0 := Real.log_nonpos hx.le hx1
  have hdiff : 0 ≤ Real.log |x|-Real.log (3/5) := by linarith
  have hmul := mul_le_mul_of_nonneg_right (show 12-72*κ ≤ (12 : ℝ) by linarith) hdiff
  nlinarith

end
end CatalanMeasure.GenD.Analytic
#print axioms CatalanMeasure.GenD.Analytic.ellipseH_le_norm_add_one
#print axioms CatalanMeasure.GenD.Analytic.real_segment_weight_le_of_power
#print axioms CatalanMeasure.GenD.Analytic.real_segment_phi_of_strong
