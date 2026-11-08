module

public import CatalanMeasure.GenD.Signed.Davis.S1RealSegments
public import CatalanMeasure.GenD.Signed.Davis.DesignWeights

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 0

namespace CatalanMeasure.GenD.Signed.Davis.RealSegmentWeights
open Set CatalanMeasure.GenD.Analytic CatalanMeasure.Refinement S1PolynomialBounds
open CatalanMeasure.Refinement.Trimmed130
noncomputable section

/-- D58 real-segment implication, independent of the retained source data. -/
theorem real_segment_weight_le_of_power58 (v : ℂ) {x H R E C B : ℝ}
    (hx : |x| ≤ 1) (hv : ‖v‖ ≤ B) (hBH : B+1 ≤ H)
    (hHR : H ≤ R) (hsq : H^2-1 ≤ (R-H)^2)
    (hpower : R^53*(4 : ℝ)^390*5^1300 ≤ E*3^1300)
    (hE : E ≤ Real.exp (130*C)) :
    (53 : ℝ)/130*ellipseLog v+6*Real.log ‖(1 : ℂ)-(x : ℂ)‖ ≤
      C+10*Real.log (3/5) := by
  have hH : ellipseH v ≤ H := (ellipseH_le_norm_add_one v).trans (by linarith)
  have hR : 0 < R := by have hh := ellipseH_ge_one v; linarith
  have hp : R^53*(4 : ℝ)^390 ≤ E*(3/5 : ℝ)^1300 := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 5^1300)).mpr hpower
    convert hh using 1 <;> rw [div_pow] <;> ring
  have hexp : Real.exp (130*(C+10*Real.log (3/5))) =
      Real.exp (130*C)*(3/5 : ℝ)^1300 := by
    rw [show 130*(C+10*Real.log (3/5 : ℝ)) =
        130*C+(1300 : ℕ)*Real.log (3/5) by norm_num; ring,
      Real.exp_add,Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 3/5)]
  have hp' : R^53*(4 : ℝ)^390 ≤ Real.exp (130*(C+10*Real.log (3/5))) := by
    rw [hexp]
    exact hp.trans (mul_le_mul_of_nonneg_right hE (by positivity))
  have hl := Real.log_le_log (mul_pos (pow_pos hR _) (by positivity : (0 : ℝ) < 4^390)) hp'
  rw [Real.log_mul (pow_pos hR _).ne' (by positivity : (4 : ℝ)^390 ≠ 0),
    Real.log_pow,Real.log_pow,Real.log_exp] at hl
  have hfour : Real.log (4 : ℝ) = 2*Real.log 2 := by
    simpa only [show (2 : ℝ)^2 = 4 by norm_num, Nat.cast_ofNat] using (Real.log_pow (2 : ℝ) 2)
  rw [hfour] at hl
  have hn : ‖(1 : ℂ)-(x : ℂ)‖ ≤ 2 := by
    have hh := norm_sub_le (1 : ℂ) (x : ℂ)
    rw [norm_one,Complex.norm_real,Real.norm_eq_abs] at hh
    linarith
  have hlog : Real.log ‖(1 : ℂ)-(x : ℂ)‖ ≤ Real.log 2 := by
    by_cases hz : ‖(1 : ℂ)-(x : ℂ)‖ = 0
    · rw [hz,Real.log_zero]
      exact Real.log_nonneg (by norm_num)
    · exact Real.log_le_log ((norm_nonneg _).lt_of_ne' hz) hn
  have hg := ellipseLog_le_log_of_square hH hHR hsq
  norm_num only [Nat.cast_ofNat] at hl
  linarith

/-- A short Taylor witness replaces a large rational exponential array. -/
theorem taylor58 : (2 : ℚ) ≤ expTaylorRat (7/10) 4 := by
  -- kcost: <0.1 s estimated; four exact rational Taylor terms.
  decide +kernel

def expLower58 : ℚ := 2^6000

theorem expLower58_le : (expLower58 : ℝ) ≤ Real.exp (130*(709/20 : ℝ)) := by
  have hb : (2 : ℝ) ≤ Real.exp (7/10 : ℝ) := by
    have hh : (2 : ℝ) ≤ (expTaylorRat (7/10) 4 : ℝ) := by exact_mod_cast taylor58
    exact hh.trans (by simpa only [Rat.cast_div,Rat.cast_ofNat] using (expTaylorRat_le_exp (x := (7/10 : ℚ)) (by norm_num) 4))
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hb 6000
  rw [← Real.exp_nat_mul] at hp
  have he : (6000 : ℝ)*(7/10) ≤ 130*(709/20 : ℝ) := by norm_num
  simpa only [expLower58,Rat.cast_pow,Rat.cast_ofNat] using hp.trans (Real.exp_le_exp.mpr he)

theorem negative_weighted_check58 :
    S1RealSegments.Negative.R^53*(4 : ℚ)^390*5^1300 ≤ expLower58*3^1300 := by
  -- kcost: <0.1 s estimated; exact comparison with a 6001-bit power of two.
  decide +kernel

theorem positive_weighted_check58 :
    S1RealSegments.Positive.R^53*(4 : ℚ)^390*5^1300 ≤ expLower58*3^1300 := by
  -- kcost: <0.1 s estimated; separate retained positive R, not negative R.
  decide +kernel
theorem Negative_segment_bound58 (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) (-3/5)) :
    (53 : ℝ)/130*ellipseLog (complexP.eval (x : ℂ))+
      6*Real.log ‖(1 : ℂ)-(x : ℂ)‖ ≤ (709/20 : ℝ)+10*Real.log (3/5) := by
  have hB : (S1RealSegments.Negative.normUpper : ℝ)+1 ≤ (S1RealSegments.Negative.H : ℝ) := by
    exact_mod_cast S1RealSegments.Negative.ellipse_check.1
  have hHR : (S1RealSegments.Negative.H : ℝ) ≤ (S1RealSegments.Negative.R : ℝ) := by
    exact_mod_cast S1RealSegments.Negative.ellipse_check.2.1
  have hsq : (S1RealSegments.Negative.H : ℝ)^2-1 ≤
      ((S1RealSegments.Negative.R : ℝ)-S1RealSegments.Negative.H)^2 := by
    exact_mod_cast S1RealSegments.Negative.ellipse_check.2.2
  have hp : (S1RealSegments.Negative.R : ℝ)^53*(4 : ℝ)^390*5^1300 ≤
      (expLower58 : ℝ)*3^1300 := by exact_mod_cast negative_weighted_check58
  have hn := S1RealSegments.Negative.norm_bound x
  have hx' : x ∈ Icc (-1 : ℝ) (-3/5) := hx
  apply real_segment_weight_le_of_power58 (v := complexP.eval (x : ℂ)) _
    (hn (by norm_num at *; exact hx)) hB hHR hsq hp expLower58_le
  apply abs_le.mpr
  constructor <;> linarith [hx'.1,hx'.2]
theorem Positive_segment_bound58 (x : ℝ) (hx : x ∈ Icc (3/5 : ℝ) 1) :
    (53 : ℝ)/130*ellipseLog (complexP.eval (x : ℂ))+
      6*Real.log ‖(1 : ℂ)-(x : ℂ)‖ ≤ (709/20 : ℝ)+10*Real.log (3/5) := by
  have hB : (S1RealSegments.Positive.normUpper : ℝ)+1 ≤ (S1RealSegments.Positive.H : ℝ) := by
    exact_mod_cast S1RealSegments.Positive.ellipse_check.1
  have hHR : (S1RealSegments.Positive.H : ℝ) ≤ (S1RealSegments.Positive.R : ℝ) := by
    exact_mod_cast S1RealSegments.Positive.ellipse_check.2.1
  have hsq : (S1RealSegments.Positive.H : ℝ)^2-1 ≤
      ((S1RealSegments.Positive.R : ℝ)-S1RealSegments.Positive.H)^2 := by
    exact_mod_cast S1RealSegments.Positive.ellipse_check.2.2
  have hp : (S1RealSegments.Positive.R : ℝ)^53*(4 : ℝ)^390*5^1300 ≤
      (expLower58 : ℝ)*3^1300 := by exact_mod_cast positive_weighted_check58
  have hn := S1RealSegments.Positive.norm_bound x
  have hx' : x ∈ Icc (3/5 : ℝ) 1 := hx
  apply real_segment_weight_le_of_power58 (v := complexP.eval (x : ℂ)) _
    (hn (by norm_num at *; exact hx)) hB hHR hsq hp expLower58_le
  apply abs_le.mpr
  constructor <;> linarith [hx'.1,hx'.2]
theorem segment_bound58 (x : ℝ) (hx0 : (3/5 : ℝ) ≤ |x|) (hx1 : |x| ≤ 1) :
    (53 : ℝ)/130*ellipseLog (complexP.eval (x : ℂ))+
      6*Real.log ‖(1 : ℂ)-(x : ℂ)‖ ≤ (709/20 : ℝ)+10*Real.log (3/5) := by
  have hx := abs_le.mp hx1
  by_cases hneg : x < 0
  · apply Negative_segment_bound58 x
    rw [abs_of_neg hneg] at hx0
    exact ⟨hx.1,by linarith⟩
  · apply Positive_segment_bound58 x
    rw [abs_of_nonneg (le_of_not_gt hneg)] at hx0
    exact ⟨hx0,hx.2⟩

theorem real_segment_phi_of_strong58 {κ x C G : ℝ} (hκ : 0 ≤ κ)
    (hx0 : (3/5 : ℝ) ≤ |x|) (hx1 : |x| ≤ 1)
    (hG : G ≤ C+10*Real.log (3/5)) :
    (10-58*κ)*Real.log |x|+G ≤ (10-58*κ)*Real.log (3/5)+C := by
  have hlo : Real.log (3/5) ≤ Real.log |x| := Real.log_le_log (by norm_num) hx0
  have hhi : Real.log |x| ≤ 0 := Real.log_nonpos (by positivity) hx1
  have hmul := mul_le_mul_of_nonneg_right (show 10-58*κ ≤ (10 : ℝ) by linarith)
    (show 0 ≤ Real.log |x|-Real.log (3/5) by linarith)
  nlinarith

theorem segmentPhi58 : ∀ κ ∈ Icc (0 : ℝ) 1, ∀ x : ℝ, (3/5 : ℝ) ≤ |x| → |x| ≤ 1 →
    nodalPhi dc58.toParameters green58 κ (x : ℂ) ≤
      (10-58*κ)*Real.log (3/5)+(709/20 : ℝ) := by
  intro κ hκ x hx0 hx1
  have hh := real_segment_phi_of_strong58 hκ.1 hx0 hx1 (segment_bound58 x hx0 hx1)
  rw [Real.log_abs] at hh
  have he : (Polynomial.aeval (x : ℂ)) realP = complexP.eval (x : ℂ) := by
    rw [Polynomial.aeval_def,Polynomial.eval₂_eq_eval_map]
    rfl
  norm_num [nodalPhi,dc58,DesignConst.toParameters,green58,nodalGreen,
    Complex.norm_real,Real.norm_eq_abs]
  rw [he]
  convert hh using 1 <;> ring

end
end CatalanMeasure.GenD.Signed.Davis.RealSegmentWeights
#print axioms CatalanMeasure.GenD.Signed.Davis.RealSegmentWeights.real_segment_weight_le_of_power58
#print axioms CatalanMeasure.GenD.Signed.Davis.RealSegmentWeights.expLower58_le
#print axioms CatalanMeasure.GenD.Signed.Davis.RealSegmentWeights.segment_bound58
#print axioms CatalanMeasure.GenD.Signed.Davis.RealSegmentWeights.segmentPhi58