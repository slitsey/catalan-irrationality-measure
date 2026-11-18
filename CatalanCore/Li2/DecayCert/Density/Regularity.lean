module
public import CatalanCore.Li2.DecayCert.Density.Base
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter Topology
open CatalanCore.Decay.ComplexEnergy
open scoped Topology
namespace CatalanCore.Li2.DecayCert

-- Generic regularity support for checkedDatum_exists, from the built BallMajA layer.
theorem log_sub_log_le_floor (ε a b : ℝ) (hε : 0<ε) (ha : ε≤a) (hab : a≤b) :
    Real.log b-Real.log a≤(b-a)/ε := by
  have ha0 : 0<a := lt_of_lt_of_le hε ha
  have hb0 : 0<b := ha0.trans_le hab
  have h := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [Real.log_div hb0.ne' ha0.ne'] at h
  have he : b/a-1=(b-a)/a := by field_simp
  rw [he] at h
  exact h.trans ((div_le_div_iff₀ ha0 hε).mpr
    (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hab)))

theorem abs_log_sub_log_le_floor (ε a b : ℝ) (hε : 0<ε) (ha : ε≤a) (hb : ε≤b) :
    |Real.log a-Real.log b|≤|a-b|/ε := by
  have ha0 : 0<a := lt_of_lt_of_le hε ha
  have hb0 : 0<b := lt_of_lt_of_le hε hb
  by_cases hab : a≤b
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ha0 hab)),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa only [neg_sub] using log_sub_log_le_floor ε a b hε ha hab
  · have hba : b≤a := le_of_not_ge hab
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb0 hba)),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    exact log_sub_log_le_floor ε b a hε hb hba

theorem clip_log_lipschitz (ε : ℝ) (hε : 0<ε) (u v s : ℂ) :
    |Real.log (max ε ‖u-s‖)-Real.log (max ε ‖v-s‖)|≤‖u-v‖/ε := by
  have h0 := abs_log_sub_log_le_floor ε (max ε ‖u-s‖) (max ε ‖v-s‖)
    hε (le_max_left _ _) (le_max_left _ _)
  have hnorm : |‖u-s‖-‖v-s‖|≤‖u-v‖ := by
    have h1 : ‖u-s‖≤‖u-v‖+‖v-s‖ := by
      calc ‖u-s‖=‖(u-v)+(v-s)‖ := by congr 1; ring
           _≤_ := norm_add_le _ _
    have h2 : ‖v-s‖≤‖u-v‖+‖u-s‖ := by
      calc ‖v-s‖=‖(v-u)+(u-s)‖ := by congr 1; ring
           _≤‖v-u‖+‖u-s‖ := norm_add_le _ _
           _=_ := by rw [norm_sub_rev v u]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hm : |max ε ‖u-s‖-max ε ‖v-s‖|≤‖u-v‖ := by
    have hh := abs_max_sub_max_le_max ε ‖u-s‖ ε ‖v-s‖
    simp only [sub_self,abs_zero] at hh
    exact hh.trans (max_le (norm_nonneg (u-v)) hnorm)
  exact h0.trans (div_le_div_of_nonneg_right hm hε.le)

theorem log_max_eq_log_add_posLog (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) :
    Real.log (max ε r)=Real.log r+Real.posLog (ε/r) := by
  rw [Real.posLog,Real.log_div hε.ne' hr.ne']
  by_cases h : ε ≤ r
  · rw [max_eq_right h,max_eq_left (sub_nonpos.mpr (Real.log_le_log hε h)),add_zero]
  · have h' : r ≤ ε := le_of_not_ge h
    rw [max_eq_left h',max_eq_right (sub_nonneg.mpr (Real.log_le_log hr h'))]
    ring

theorem clipped_log_integrable (σ : Measure ℂ) [IsFiniteMeasure σ]
    (b A α : ℝ) (hσ : BallMajA σ b A α) (ε : ℝ) (hε : 0 < ε) (u : ℂ) :
    Integrable (fun s => Real.log (max ε ‖u-s‖)) σ := by
  have hi := (integrable_log_norm_sub hσ u).add (integrable_regC hσ hε u)
  apply hi.congr
  have hae : ∀ᵐ s ∂σ, s ≠ u := by
    exact measure_eq_zero_iff_ae_notMem.mp (hσ.singleton_zero u)
  filter_upwards [hae] with s hs
  have hr : 0 < ‖u-s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hs))
  exact (log_max_eq_log_add_posLog ε ‖u-s‖ hε hr).symm

theorem clipped_log_error (σ : Measure ℂ) [IsFiniteMeasure σ]
    (b A α : ℝ) (hσ : BallMajA σ b A α) (ε : ℝ) (hε : 0 < ε) (u : ℂ) :
    |(∫ s, Real.log (max ε ‖u-s‖) ∂σ)-(∫ s,Real.log ‖u-s‖ ∂σ)| ≤ A*ε^α/α := by
  have hae : ∀ᵐ s ∂σ, Real.log (max ε ‖u-s‖)=Real.log ‖u-s‖+regC u ε s := by
    have hne : ∀ᵐ s ∂σ, s ≠ u := measure_eq_zero_iff_ae_notMem.mp (hσ.singleton_zero u)
    filter_upwards [hne] with s hs
    exact log_max_eq_log_add_posLog ε _ hε (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hs)))
  rw [integral_congr_ae hae,integral_add (integrable_log_norm_sub hσ u) (integrable_regC hσ hε u),
    add_sub_cancel_left,abs_of_nonneg (integral_nonneg (fun s => regC_nonneg u ε s))]
  exact integral_regC_le hσ hε u

theorem clipped_log_difference (σ : Measure ℂ) [IsFiniteMeasure σ]
    (b A α : ℝ) (hσ : BallMajA σ b A α) (ε : ℝ) (hε : 0 < ε) (u v : ℂ) :
    |(∫ s,Real.log (max ε ‖u-s‖) ∂σ)-(∫ s,Real.log (max ε ‖v-s‖) ∂σ)| ≤
      σ.real univ*‖u-v‖/ε := by
  rw [← integral_sub (clipped_log_integrable σ b A α hσ ε hε u) (clipped_log_integrable σ b A α hσ ε hε v)]
  apply (abs_integral_le_integral_abs).trans
  have hi := integral_mono_ae
    (((clipped_log_integrable σ b A α hσ ε hε u).sub (clipped_log_integrable σ b A α hσ ε hε v)).abs)
    (integrable_const (‖u-v‖/ε)) (Filter.Eventually.of_forall (fun s => clip_log_lipschitz ε hε u v s))
  rw [integral_const,smul_eq_mul] at hi
  simpa only [Pi.sub_apply,mul_div_assoc] using hi

theorem ballMajA_potential_holder_third (σ : Measure ℂ) [IsFiniteMeasure σ]
    (b A : ℝ) (hσ : BallMajA σ b A (1/2)) (u v : ℂ) :
    |potC σ u-potC σ v| ≤ (4*A+σ.real univ)*‖u-v‖^((1:ℝ)/3) := by
  by_cases huv : u=v
  · subst v
    simp only [sub_self,abs_zero,norm_zero,Real.zero_rpow (by norm_num : (1:ℝ)/3 ≠ 0),mul_zero,le_refl]
  have ht : 0 < ‖u-v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huv)
  let ε : ℝ := ‖u-v‖^((2:ℝ)/3)
  have hε : 0 < ε := Real.rpow_pos_of_pos ht _
  have hpow : ε^((1:ℝ)/2)=‖u-v‖^((1:ℝ)/3) := by
    dsimp only [ε]
    rw [← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have hdiv : ‖u-v‖/ε=‖u-v‖^((1:ℝ)/3) := by
    calc
      ‖u-v‖/ε=(‖u-v‖^((1:ℝ)))/(‖u-v‖^((2:ℝ)/3)) := by rw [Real.rpow_one]
      _ = ‖u-v‖^((1:ℝ)-2/3) := (Real.rpow_sub ht _ _).symm
      _ = ‖u-v‖^((1:ℝ)/3) := by norm_num
  have herr : A*ε^((1:ℝ)/2)/((1:ℝ)/2)=2*A*‖u-v‖^((1:ℝ)/3) := by rw [hpow]; ring
  have h1 := clipped_log_error σ b A (1/2) hσ ε hε u
  have h2 := clipped_log_error σ b A (1/2) hσ ε hε v
  have h3 := clipped_log_difference σ b A (1/2) hσ ε hε u v
  rw [herr] at h1 h2
  rw [mul_div_assoc,hdiv] at h3
  let P : ℂ → ℝ := fun t => ∫ s,Real.log ‖t-s‖ ∂σ
  let C : ℂ → ℝ := fun t => ∫ s,Real.log (max ε ‖t-s‖) ∂σ
  have he : P u-P v=(P u-C u)+(C u-C v)+(C v-P v) := by ring
  have htri : |P u-P v| ≤ |P u-C u|+|C u-C v|+|C v-P v| := by
    rw [he]
    have ha := abs_add_le (P u-C u) (C u-C v)
    have hb := abs_add_le ((P u-C u)+(C u-C v)) (C v-P v)
    linarith
  change |P u-P v| ≤ _
  change |C u-P u| ≤ _ at h1
  change |C v-P v| ≤ _ at h2
  change |C u-C v| ≤ _ at h3
  rw [abs_sub_comm (P u) (C u)] at htri
  nlinarith

theorem datum_of_ballMajA_exists (σ : Measure ℂ) [IsFiniteMeasure σ]
    (b A : ℝ) (hσ : BallMajA σ b A (1/2)) (hmass : σ.real univ=2) :
    ∃ d : CatalanCore.Li2.Uniform.DualDatum, d.σ=σ := by
  have hpot (u : ℂ) : CatalanCore.Li2.Uniform.pot σ u= -potC σ u := by
    change (∫ s,-Real.log ‖u-s‖ ∂σ)= -∫ s,Real.log ‖u-s‖ ∂σ
    exact integral_neg _
  refine ⟨{ σ := σ
            finite := inferInstance
            mass := hmass
            radius := b
            radius_nonneg := hσ.b_pos.le
            bounded := hσ.ae_mem
            holderExponent := (1:ℝ)/3
            holderPos := by norm_num
            holderLe := by norm_num
            holderConstant := ⟨4*A+2,by linarith [hσ.A_nonneg]⟩
            holder := ?_
            pointLogIntegrable := integrable_log_norm_sub hσ
            selfIntegrable := integrable_sigma_sigma hσ
            selfDistinct := CatalanCore.Zeta5.Energy.ae_ne_of_noAtoms_right hσ.singleton_zero },rfl⟩
  intro u v
  change |CatalanCore.Li2.Uniform.pot σ u-CatalanCore.Li2.Uniform.pot σ v| ≤
    (4*A+2)*‖u-v‖^((1:ℝ)/3)
  rw [hpot,hpot,neg_sub_neg,abs_sub_comm]
  simpa only [hmass] using ballMajA_potential_holder_third σ b A hσ u v

#print axioms datum_of_ballMajA_exists

#print axioms ballMajA_potential_holder_third

#print axioms log_max_eq_log_add_posLog
#print axioms clipped_log_integrable
#print axioms clipped_log_error
#print axioms clipped_log_difference

#print axioms clip_log_lipschitz
end CatalanCore.Li2.DecayCert
