module
public import CatalanCore.Li2.Uniform.Spec
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
@[expose] public section
/-! Closure of the canonical dual datum and cap integrability. Exact W1 rows; no certificate assumptions. -/
set_option Elab.async false
open MeasureTheory Set Filter Complex
open scoped Topology
namespace CatalanCore.Li2.Uniform

theorem datum_continuous_pot (d : DualDatum) : Continuous (pot d.σ) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  have hb : Tendsto (fun u : ℂ => (d.holderConstant : ℝ) * ‖u-v‖ ^ d.holderExponent)
      (𝓝 v) (𝓝 0) := by
    have h : ContinuousAt (fun u : ℂ => (d.holderConstant : ℝ) * ‖u-v‖ ^ d.holderExponent) v := continuousAt_const.mul
      ((continuousAt_id.sub continuousAt_const).norm.rpow_const (Or.inr d.holderPos.le))
    simpa [Real.zero_rpow d.holderPos.ne'] using h.tendsto
  have hz : Tendsto (fun u : ℂ => ‖pot d.σ u - pot d.σ v‖) (𝓝 v) (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun u => by simpa [Real.norm_eq_abs] using d.holder u v) hb
  exact (tendsto_iff_norm_sub_tendsto_zero.mpr hz)

theorem datum_energy_integrable (d : DualDatum) : Integrable (pot d.σ) d.σ := by
  change Integrable (fun x : ℂ => ∫ y, -Real.log ‖x-y‖ ∂d.σ) d.σ
  simpa only [Pi.neg_apply] using d.selfIntegrable.neg.integral_prod_left

theorem datum_atomless (d : DualDatum) (z : ℂ) : d.σ {z} = 0 := by
  have hz : (d.σ.prod d.σ) ({z} ×ˢ {z}) = 0 := by
    apply measure_mono_null (t := {p : ℂ × ℂ | ¬ p.1 ≠ p.2})
    · intro p hp
      rcases hp with ⟨hp,hq⟩
      simp only [mem_singleton_iff] at hp hq
      simp [hp,hq]
    · exact ae_iff.mp d.selfDistinct
  rw [Measure.prod_prod] at hz
  exact (mul_eq_zero.mp hz).elim id id

theorem datum_cross_distinct (d0 d1 : DualDatum) :
    ∀ᵐ p ∂(d0.σ.prod d1.σ), p.1 ≠ p.2 := by
  exact CatalanCore.Zeta5.Energy.ae_ne_of_noAtoms_right (datum_atomless d1)

private theorem datum_abs_log_bound (d : DualDatum) (R : ℝ) (hR : 0 ≤ R)
    (w : ℂ) (hw : ‖w‖ ≤ R) :
    (∫ z, |Real.log ‖z-w‖| ∂d.σ) ≤
      4 * (1 + d.radius + R) + |pot d.σ 0| +
        (d.holderConstant : ℝ) * R ^ d.holderExponent := by
  let L := 1 + d.radius + R
  have hi : Integrable (fun z : ℂ => Real.log ‖z-w‖) d.σ := by
    simpa only [norm_sub_rev] using d.pointLogIntegrable w
  have hm : Integrable (fun z : ℂ => max (Real.log ‖z-w‖) 0) d.σ := by
    have he : (fun z : ℂ => max (Real.log ‖z-w‖) 0) =
        (fun z => (Real.log ‖z-w‖ + |Real.log ‖z-w‖|) / 2) := by
      funext z
      by_cases h : 0 ≤ Real.log ‖z-w‖
      · rw [max_eq_left h, abs_of_nonneg h]; ring
      · rw [max_eq_right (le_of_not_ge h), abs_of_nonpos (le_of_not_ge h)]; ring
    rw [he]
    exact (hi.add hi.abs).div_const 2
  have hb : (∫ z, max (Real.log ‖z-w‖) 0 ∂d.σ) ≤ 2*L := by
    have hh := integral_mono_ae hm (integrable_const L) (by
      filter_upwards [d.bounded] with z hz
      apply max_le
      · exact (Real.log_le_self (norm_nonneg _)).trans
          ((norm_sub_le z w).trans (by dsimp [L]; linarith))
      · dsimp [L]; linarith [d.radius_nonneg])
    simpa only [integral_const, smul_eq_mul, d.mass] using hh
  have he : (∫ z, |Real.log ‖z-w‖| ∂d.σ) =
      2 * (∫ z, max (Real.log ‖z-w‖) 0 ∂d.σ) + pot d.σ w := by
    have hpoint : (fun z : ℂ => |Real.log ‖z-w‖|) =
        (fun z => 2 * max (Real.log ‖z-w‖) 0 - Real.log ‖z-w‖) := by
      funext z
      by_cases h : 0 ≤ Real.log ‖z-w‖
      · rw [abs_of_nonneg h, max_eq_left h]; ring
      · rw [abs_of_nonpos (le_of_not_ge h), max_eq_right (le_of_not_ge h)]; ring
    rw [hpoint, integral_sub (hm.const_mul 2) hi, integral_const_mul]
    have hp : pot d.σ w = -(∫ z, Real.log ‖z-w‖ ∂d.σ) := by
      change (∫ z, -Real.log ‖w-z‖ ∂d.σ) = _
      rw [integral_neg]
      simp only [norm_sub_rev]
    linarith
  have hp : pot d.σ w ≤ |pot d.σ 0| + (d.holderConstant : ℝ) * R ^ d.holderExponent := by
    have hh := d.holder w 0
    simp only [sub_zero] at hh
    have hr := Real.rpow_le_rpow (norm_nonneg w) hw d.holderPos.le
    have hm' := mul_le_mul_of_nonneg_left hr d.holderConstant.coe_nonneg
    have hs := le_abs_self (pot d.σ w - pot d.σ 0)
    have hz := le_abs_self (pot d.σ 0)
    linarith
  rw [he]
  dsimp only [L] at hb
  linarith

theorem datum_cross_log_integrable (d0 d1 : DualDatum) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (d0.σ.prod d1.σ) := by
  apply CatalanCore.Zeta5.Energy.integrable_log_prod
    (C := 4 * (1 + d0.radius + d1.radius) + |pot d0.σ 0| +
      (d0.holderConstant : ℝ) * d1.radius ^ d0.holderExponent)
  · exact ae_of_all _ fun w => by simpa only [norm_sub_rev] using d0.pointLogIntegrable w
  · filter_upwards [d1.bounded] with w hw
    exact datum_abs_log_bound d0 d1.radius d1.radius_nonneg w hw


private theorem negpart_eq (x : ℝ) : max (-x) 0 = (|x|-x)/2 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_right (neg_nonpos.mpr hx)]; ring
  · rw [abs_of_nonpos (le_of_not_ge hx), max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))]; ring

private theorem datum_negpart_integrable (d : DualDatum) (u : ℂ) :
    Integrable (fun y => max (-Real.log ‖u-y‖) 0) d.σ := by
  simp_rw [negpart_eq]
  exact ((d.pointLogIntegrable u).abs.sub (d.pointLogIntegrable u)).div_const 2

private theorem datum_negpart_uniform (d : DualDatum) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℂ, (∫ y, max (-Real.log ‖u-y‖) 0 ∂d.σ) ≤ M := by
  have hrad := d.radius_nonneg
  let M := 4 * (1 + d.radius + (d.radius+1)) + |pot d.σ 0| +
    (d.holderConstant : ℝ) * (d.radius+1) ^ d.holderExponent
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro u
  by_cases hu : ‖u‖ ≤ d.radius+1
  · have hh := datum_abs_log_bound d (d.radius+1) (by linarith [d.radius_nonneg]) u hu
    have hm := integral_mono_ae (datum_negpart_integrable d u) (d.pointLogIntegrable u).abs
      (ae_of_all _ fun y => by
        apply max_le
        · exact neg_le_abs _
        · exact abs_nonneg _)
    have he : (∫ z, |Real.log ‖z-u‖| ∂d.σ) = ∫ z, |Real.log ‖u-z‖| ∂d.σ := by
      simp only [norm_sub_rev]
    rw [he] at hh
    exact hm.trans hh
  · have he : (∫ y, max (-Real.log ‖u-y‖) 0 ∂d.σ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [d.bounded] with y hy
      have ht := norm_sub_norm_le u y
      have hnorm : 1 ≤ ‖u-y‖ := by linarith
      simp only [max_eq_right (neg_nonpos.mpr (Real.log_nonneg hnorm)), Pi.zero_apply]
    rw [he]
    dsimp [M]; positivity

private theorem log_diff_le_negpart (a b h : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hh : 0 ≤ h) (hab : b ≤ a+h) :
    Real.log b - Real.log a ≤ max (-Real.log a) 0 + Real.log (1+h) := by
  have hp : Real.log b ≤ max (Real.log a) 0 + Real.log (1+h) := by
    by_cases hb0 : b = 0
    · rw [hb0, Real.log_zero]
      exact add_nonneg (le_max_right _ _) (Real.log_nonneg (by linarith))
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      by_cases ha1 : a ≤ 1
      · have hx := Real.log_le_log hbpos (hab.trans (by linarith : a+h ≤ 1+h))
        linarith [le_max_right (Real.log a) 0]
      · have ha' : 1 < a := lt_of_not_ge ha1
        have hmul : a+h ≤ a*(1+h) := by nlinarith
        have hx := Real.log_le_log hbpos (hab.trans hmul)
        rw [Real.log_mul (by linarith) (by linarith)] at hx
        linarith [le_max_left (Real.log a) 0]
  by_cases hx : 0 ≤ Real.log a
  · rw [max_eq_right (neg_nonpos.mpr hx)]
    rw [max_eq_left hx] at hp
    linarith
  · rw [max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))]
    rw [max_eq_right (le_of_not_ge hx)] at hp
    linarith


private theorem datum_pot_diff_log_bound (d : DualDatum) (M : ℝ)
    (hM : ∀ u : ℂ, (∫ y, max (-Real.log ‖u-y‖) 0 ∂d.σ) ≤ M) (u v : ℂ) :
    pot d.σ u - pot d.σ v ≤ M + 2*Real.log (1+‖u-v‖) := by
  have hp : pot d.σ u - pot d.σ v =
      ∫ y, Real.log ‖v-y‖ - Real.log ‖u-y‖ ∂d.σ := by
    change (∫ y, -Real.log ‖u-y‖ ∂d.σ) - (∫ y, -Real.log ‖v-y‖ ∂d.σ) = _
    rw [integral_neg, integral_neg, integral_sub (d.pointLogIntegrable v) (d.pointLogIntegrable u)]
    ring
  rw [hp]
  have hm := integral_mono_ae ((d.pointLogIntegrable v).sub (d.pointLogIntegrable u))
    ((datum_negpart_integrable d u).add (integrable_const (Real.log (1+‖u-v‖))))
    (ae_of_all _ fun y => log_diff_le_negpart ‖u-y‖ ‖v-y‖ ‖u-v‖
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (by
        have ht := norm_add_le (v-u) (u-y)
        rw [sub_add_sub_cancel] at ht
        rw [norm_sub_rev v u] at ht
        linarith))
  dsimp only [Pi.add_apply, Pi.sub_apply] at hm
  rw [integral_add (datum_negpart_integrable d u) (integrable_const _), integral_const,
    smul_eq_mul, d.mass] at hm
  linarith [hM u]

theorem datum_holder_downgrade (d : DualDatum) (β : ℝ)
    (hβ : 0 < β) (hle : β ≤ d.holderExponent) :
    ∃ C : NNReal, ∀ u v : ℂ,
      |pot d.σ u - pot d.σ v| ≤ (C : ℝ) * ‖u-v‖ ^ β := by
  obtain ⟨M,hM0,hM⟩ := datum_negpart_uniform d
  let K := (d.holderConstant : ℝ) + M + 2*Real.log 2 + 2/β
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨⟨K,hK0⟩, ?_⟩
  intro u v
  change |pot d.σ u - pot d.σ v| ≤ K * ‖u-v‖ ^ β
  by_cases hn : ‖u-v‖ ≤ 1
  · have hr := Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (u-v)) hn hβ.le hle
    calc
      |pot d.σ u - pot d.σ v| ≤ (d.holderConstant : ℝ) * ‖u-v‖ ^ d.holderExponent := d.holder u v
      _ ≤ (d.holderConstant : ℝ) * ‖u-v‖ ^ β := mul_le_mul_of_nonneg_left hr d.holderConstant.coe_nonneg
      _ ≤ K * ‖u-v‖ ^ β := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
        dsimp [K]; linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 2) hβ.le]
  · have hh : 1 ≤ ‖u-v‖ := le_of_lt (lt_of_not_ge hn)
    have hr := Real.one_le_rpow hh hβ.le
    have hl : Real.log (1+‖u-v‖) ≤ Real.log 2 + ‖u-v‖ ^ β / β := by
      calc
        Real.log (1+‖u-v‖) ≤ Real.log (2*‖u-v‖) :=
          Real.log_le_log (by positivity) (by linarith)
        _ = Real.log 2 + Real.log ‖u-v‖ := Real.log_mul (by norm_num) (by linarith)
        _ ≤ Real.log 2 + ‖u-v‖ ^ β / β := add_le_add (le_refl (Real.log 2)) (Real.log_le_rpow_div (x := ‖u-v‖) (norm_nonneg _) hβ)
    have hu := datum_pot_diff_log_bound d M hM u v
    have hv := datum_pot_diff_log_bound d M hM v u
    rw [norm_sub_rev v u] at hv
    have ha : |pot d.σ u - pot d.σ v| ≤ M+2*Real.log (1+‖u-v‖) := by
      apply abs_le.mpr
      constructor <;> linarith
    have hmul : M + 2*Real.log 2 ≤ (M+2*Real.log 2)*‖u-v‖^β :=
      le_mul_of_one_le_right (by positivity) hr
    have hc : 0 ≤ (d.holderConstant : ℝ) * ‖u-v‖ ^ β := by positivity
    dsimp only [K]
    have he : 2*(‖u-v‖^β/β) = (2/β)*‖u-v‖^β := by ring
    nlinarith


theorem pot_mix_measure (l : ℝ) (hl : l ∈ Icc 0 1) (d0 d1 : DualDatum) (u : ℂ) :
    pot (ENNReal.ofReal l • d0.σ + ENNReal.ofReal (1-l) • d1.σ) u =
      l * pot d0.σ u + (1-l) * pot d1.σ u := by
  change (∫ y, -Real.log ‖u-y‖ ∂(ENNReal.ofReal l • d0.σ + ENNReal.ofReal (1-l) • d1.σ)) = _
  have hi0 : Integrable (fun y => -Real.log ‖u-y‖) (ENNReal.ofReal l • d0.σ) := by
    have hh : Integrable (fun y => Real.log ‖u-y‖) (ENNReal.ofReal l • d0.σ) :=
      (d0.pointLogIntegrable u).smul_measure ENNReal.ofReal_ne_top
    exact hh.neg
  have hi1 : Integrable (fun y => -Real.log ‖u-y‖) (ENNReal.ofReal (1-l) • d1.σ) := by
    have hh : Integrable (fun y => Real.log ‖u-y‖) (ENNReal.ofReal (1-l) • d1.σ) :=
      (d1.pointLogIntegrable u).smul_measure ENNReal.ofReal_ne_top
    exact hh.neg
  rw [integral_add_measure hi0 hi1]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal hl.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hl.2), smul_eq_mul]
  rfl

theorem mixDatum_exists (l : ℝ) (hl : l ∈ Icc 0 1) (d0 d1 : DualDatum) :
    ∃ d : DualDatum, d.σ = ENNReal.ofReal l • d0.σ + ENNReal.ofReal (1-l) • d1.σ := by
  have hl0 := hl.1
  have hl1 := sub_nonneg.mpr hl.2
  let c := ENNReal.ofReal l
  let e := ENNReal.ofReal (1-l)
  have hc : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have he : e ≠ ⊤ := ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (c • d0.σ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top _ _)⟩
  haveI : IsFiniteMeasure (e • d1.σ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top he.lt_top (measure_lt_top _ _)⟩
  let μ := c • d0.σ + e • d1.σ
  have hμ : μ.real univ = 2 := by
    dsimp only [μ]
    rw [measureReal_add_apply]
    simp only [measureReal_ennreal_smul_apply, c, e, ENNReal.toReal_ofReal hl.1,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hl.2), d0.mass, d1.mass]
    ring
  let β := min d0.holderExponent d1.holderExponent
  have hβ : 0 < β := lt_min d0.holderPos d1.holderPos
  obtain ⟨C0,hC0⟩ := datum_holder_downgrade d0 β hβ (min_le_left _ _)
  obtain ⟨C1,hC1⟩ := datum_holder_downgrade d1 β hβ (min_le_right _ _)
  let C : NNReal := ⟨l*(C0:ℝ)+(1-l)*(C1:ℝ), by positivity⟩
  have hhold : ∀ u v : ℂ, |pot μ u-pot μ v| ≤ (C:ℝ)*‖u-v‖^β := by
    intro u v
    change |pot (ENNReal.ofReal l • d0.σ + ENNReal.ofReal (1-l) • d1.σ) u -
      pot (ENNReal.ofReal l • d0.σ + ENNReal.ofReal (1-l) • d1.σ) v| ≤ _
    rw [pot_mix_measure l hl d0 d1 u, pot_mix_measure l hl d0 d1 v]
    have heq : l*pot d0.σ u+(1-l)*pot d1.σ u - (l*pot d0.σ v+(1-l)*pot d1.σ v) =
        l*(pot d0.σ u-pot d0.σ v)+(1-l)*(pot d1.σ u-pot d1.σ v) := by ring
    rw [heq]
    have hh := abs_add_le (l*(pot d0.σ u-pot d0.σ v)) ((1-l)*(pot d1.σ u-pot d1.σ v))
    rw [abs_mul, abs_mul, abs_of_nonneg hl.1, abs_of_nonneg (sub_nonneg.mpr hl.2)] at hh
    have hh0 := mul_le_mul_of_nonneg_left (hC0 u v) hl.1
    have hh1 := mul_le_mul_of_nonneg_left (hC1 u v) (sub_nonneg.mpr hl.2)
    change _ ≤ (l*(C0:ℝ)+(1-l)*(C1:ℝ))*‖u-v‖^β
    nlinarith
  have hbound : ∀ᵐ z ∂μ, ‖z‖ ≤ max d0.radius d1.radius := by
    apply ae_add_measure_iff.mpr
    constructor
    · exact Measure.ae_smul_measure (d0.bounded.mono fun _ hz => hz.trans (le_max_left _ _)) c
    · exact Measure.ae_smul_measure (d1.bounded.mono fun _ hz => hz.trans (le_max_right _ _)) e
  have hpoint : ∀ u : ℂ, Integrable (fun y => Real.log ‖u-y‖) μ := by
    intro u
    exact integrable_add_measure.mpr ⟨(d0.pointLogIntegrable u).smul_measure hc,
      (d1.pointLogIntegrable u).smul_measure he⟩
  have hprod : μ.prod μ =
      c • (c • (d0.σ.prod d0.σ) + e • (d0.σ.prod d1.σ)) +
      e • (c • (d1.σ.prod d0.σ) + e • (d1.σ.prod d1.σ)) := by
    dsimp only [μ]
    rw [Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
      Measure.prod_add, Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right,
      Measure.prod_smul_right, Measure.prod_smul_right]
  have hself : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) (μ.prod μ) := by
    rw [hprod]
    exact integrable_add_measure.mpr ⟨
      (integrable_add_measure.mpr ⟨d0.selfIntegrable.smul_measure hc,
        (datum_cross_log_integrable d0 d1).smul_measure he⟩).smul_measure hc,
      (integrable_add_measure.mpr ⟨(datum_cross_log_integrable d1 d0).smul_measure hc,
        d1.selfIntegrable.smul_measure he⟩).smul_measure he⟩
  have hdist : ∀ᵐ p ∂(μ.prod μ), p.1 ≠ p.2 := by
    rw [hprod]
    exact ae_add_measure_iff.mpr ⟨
      Measure.ae_smul_measure (ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure d0.selfDistinct c,
        Measure.ae_smul_measure (datum_cross_distinct d0 d1) e⟩) c,
      Measure.ae_smul_measure (ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure (datum_cross_distinct d1 d0) c,
        Measure.ae_smul_measure d1.selfDistinct e⟩) e⟩
  exact ⟨{ σ := μ
           finite := inferInstance
           mass := hμ
           radius := max d0.radius d1.radius
           radius_nonneg := d0.radius_nonneg.trans (le_max_left _ _)
           bounded := hbound
           holderExponent := β
           holderPos := hβ
           holderLe := (min_le_left _ _).trans d0.holderLe
           holderConstant := C
           holder := hhold
           pointLogIntegrable := hpoint
           selfIntegrable := hself
           selfDistinct := hdist }, rfl⟩
noncomputable def mixDatum (l : ℝ) (hl : l ∈ Icc 0 1) (d0 d1 : DualDatum) : DualDatum :=
  Classical.choose (mixDatum_exists l hl d0 d1)
theorem mixDatum_measure (l : ℝ) (hl : l ∈ Icc 0 1) (d0 d1 : DualDatum) :
    (mixDatum l hl d0 d1).σ = ENNReal.ofReal l • d0.σ + ENNReal.ofReal (1-l) • d1.σ :=
  Classical.choose_spec (mixDatum_exists l hl d0 d1)


private theorem real_log_integral (x b : ℝ) :
    (∫ y in (0:ℝ)..b, Real.log ‖(x:ℂ)+(y:ℂ)‖) =
      (x+b)*Real.log (x+b) - x*Real.log x - b := by
  have he : (fun y : ℝ => Real.log ‖(x:ℂ)+(y:ℂ)‖) = (fun y => Real.log (x+y)) := by
    funext y
    rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
  rw [he, intervalIntegral.integral_comp_add_left, integral_log]
  simp only [add_zero, zero_add]
  ring

private theorem phi0_real_continuous : Continuous (fun x : ℝ => phi0 (x:ℂ)) := by
  have he : (fun x : ℝ => phi0 (x:ℂ)) = (fun x =>
      3 * ((x+1)*Real.log (x+1) - x*Real.log x - 1) -
      ((x+4)*Real.log (x+4) - x*Real.log x - 4)) := by
    funext x
    change 3 * (∫ y in (0:ℝ)..1, Real.log ‖(x:ℂ)+(y:ℂ)‖) -
      (∫ y in (0:ℝ)..4, Real.log ‖(x:ℂ)+(y:ℂ)‖) = _
    rw [real_log_integral, real_log_integral]
  rw [he]
  exact (((Real.continuous_mul_log.comp (continuous_id.add continuous_const)).sub
    Real.continuous_mul_log).sub continuous_const).const_mul 3 |>.sub
    (((Real.continuous_mul_log.comp (continuous_id.add continuous_const)).sub
      Real.continuous_mul_log).sub continuous_const)

private theorem W_real_continuous (s : ℤ) (t : ℝ) (d : DualDatum) :
    Continuous (fun x : ℝ => W s t d (x:ℂ)) := by
  have he : (fun x : ℝ => W s t d (x:ℂ)) =
      (fun x : ℝ => phi0 (x:ℂ) - t*x - 2*pot d.σ (x:ℂ)) := by
    funext x
    simp only [W, Complex.ofReal_re, Complex.ofReal_im, abs_zero, mul_zero, sub_zero]
  rw [he]
  exact (phi0_real_continuous.sub (continuous_const.mul continuous_id)).sub
    (continuous_const.mul ((datum_continuous_pot d).comp Complex.continuous_ofReal))

private theorem A_real_continuous (t r : ℝ) (d : DualDatum) : Continuous (A t r d) := by
  have he : A t r d = (fun x => phi0 ((-x:ℝ):ℂ) + t*x-r-2*pot d.σ ((-x:ℝ):ℂ)) := by
    funext x
    simp only [A, Complex.ofReal_neg]
  rw [he]
  exact (((phi0_real_continuous.comp continuous_neg).add (continuous_const.mul continuous_id)).sub
    continuous_const).sub (continuous_const.mul ((datum_continuous_pot d).comp
      (Complex.continuous_ofReal.comp continuous_neg)))


private theorem W_real_tail_bound (s : ℤ) (t : ℝ) (d : DualDatum) (x : ℝ) (hx : 1 ≤ x) :
    W s t d (x:ℂ) ≤ 7 * Real.log (x+d.radius+1) - t*x := by
  have hrad := d.radius_nonneg
  have he (b : ℝ) : (fun y : ℝ => Real.log ‖(x:ℂ)+(y:ℂ)‖) = (fun y => Real.log (x+y)) := by
    funext y
    rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
  have hi : IntervalIntegrable (fun y : ℝ => Real.log (x+y)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.log (continuous_const.add continuous_id).continuousOn
    intro y hy
    simp only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), mem_Icc] at hy
    change x+y ≠ 0
    linarith
  have hu := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 1) (by norm_num) hi
    (intervalIntegrable_const (c := Real.log (x+1))) (fun y hy =>
      Real.log_le_log (by linarith [hy.1]) (by linarith [hy.2]))
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hu
  have hl : 0 ≤ ∫ y in (0:ℝ)..4, Real.log (x+y) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro y hy
    apply Real.log_nonneg
    linarith [hy.1]
  have hp : (∫ y, Real.log ‖(x:ℂ)-y‖ ∂d.σ) ≤ 2*Real.log (x+d.radius+1) := by
    have hh := integral_mono_ae (d.pointLogIntegrable (x:ℂ))
      (integrable_const (Real.log (x+d.radius+1))) (by
        filter_upwards [d.bounded] with y hy
        have hn : ‖(x:ℂ)-y‖ ≤ x+d.radius+1 := by
          have ht := norm_sub_le (x:ℂ) y
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x)] at ht
          linarith
        by_cases hz : ‖(x:ℂ)-y‖ = 0
        · rw [hz, Real.log_zero]
          exact Real.log_nonneg (by linarith)
        · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)) hn)
    simpa only [integral_const, smul_eq_mul, d.mass] using hh
  have hp' : pot d.σ (x:ℂ) = -(∫ y, Real.log ‖(x:ℂ)-y‖ ∂d.σ) := by
    change (∫ y, -Real.log ‖(x:ℂ)-y‖ ∂d.σ) = _
    rw [integral_neg]
  have hlog : Real.log (x+1) ≤ Real.log (x+d.radius+1) :=
    Real.log_le_log (by linarith) (by linarith)
  change (3 * (∫ y in (0:ℝ)..1, Real.log ‖(x:ℂ)+(y:ℂ)‖) -
    (∫ y in (0:ℝ)..4, Real.log ‖(x:ℂ)+(y:ℂ)‖)) - t*(x:ℂ).re -
    (if s=1 then 2*Real.pi else Real.pi)*|(x:ℂ).im| - 2*pot d.σ (x:ℂ) ≤ _
  simp only [Complex.ofReal_re, Complex.ofReal_im, abs_zero, mul_zero, sub_zero, hp']
  simp_rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
  linarith


private theorem W_real_eventually_le (s : ℤ) (t : ℝ) (ht : 0 < t)
    (d : DualDatum) (θ : ℝ) : ∀ᶠ x : ℝ in atTop, W s t d (x:ℂ) ≤ θ := by
  have he := Real.isLittleO_log_id_atTop.bound (show 0 < t/28 by positivity)
  have hs : Tendsto (fun x : ℝ => x+d.radius+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_atTop_add_const_right atTop d.radius tendsto_id)
  have he' := hs.eventually he
  filter_upwards [he', eventually_ge_atTop (max 1 (d.radius+1)),
    eventually_ge_atTop (-2*θ/t)] with x hx hx0 hxθ
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx0
  have hxR : d.radius+1 ≤ x := (le_max_right _ _).trans hx0
  have hpos : 0 ≤ x+d.radius+1 := by linarith [d.radius_nonneg]
  have hlog : Real.log (x+d.radius+1) ≤ (t/28)*(x+d.radius+1) := by
    have hh := (le_abs_self (Real.log (x+d.radius+1))).trans hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hpos, id_eq] using hh
  have hθ : -2*θ ≤ x*t := (div_le_iff₀ ht).mp hxθ
  have hh := W_real_tail_bound s t d x hx1
  have hm := mul_le_mul_of_nonneg_left (show x+d.radius+1 ≤ 2*x by linarith) ht.le
  nlinarith

theorem cap_integrable (F : DualFrame) (g : FrameGeometry F) (s : ℤ)
    (t r : ℝ) (ht : 0 < t) (d : DualDatum) (θ : ℝ) :
    CapIntegrable F s t r d θ := by
  have hcont : Continuous (fun x : ℝ => max (W s t d (x:ℂ)-θ) 0) :=
    ((W_real_continuous s t d).sub continuous_const).max continuous_const
  constructor
  · rcases F.lattice_kind with hlat | ⟨c,hc,hlat⟩
    · rw [hlat]
      obtain ⟨B,hB⟩ := eventually_atTop.mp (W_real_eventually_le s t ht d θ)
      let b := max 0 B
      have hzero : IntegrableOn (fun x : ℝ => max (W s t d (x:ℂ)-θ) 0) (Ici b) := by
        apply (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0:ℝ)) (Ici b) volume).congr_fun _ measurableSet_Ici
        intro x hx
        have hh := hB x ((le_max_right _ _).trans hx)
        simp only [max_eq_right (sub_nonpos.mpr hh)]
      have hcompact : IntegrableOn (fun x : ℝ => max (W s t d (x:ℂ)-θ) 0) (Icc 0 b) volume :=
        hcont.continuousOn.integrableOn_compact isCompact_Icc
      have hall := integrableOn_union.mpr ⟨hcompact,hzero⟩
      apply hall.mono_set
      intro x hx
      by_cases hxb : x ≤ b
      · exact Or.inl ⟨hx,hxb⟩
      · exact Or.inr (le_of_lt (lt_of_not_ge hxb))
    · rw [hlat]
      exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  · exact (((A_real_continuous t r d).sub continuous_const).max continuous_const).intervalIntegrable 1 4

end CatalanCore.Li2.Uniform
#print axioms CatalanCore.Li2.Uniform.datum_continuous_pot
#print axioms CatalanCore.Li2.Uniform.datum_energy_integrable
#print axioms CatalanCore.Li2.Uniform.datum_atomless
#print axioms CatalanCore.Li2.Uniform.datum_cross_distinct

#print axioms CatalanCore.Li2.Uniform.datum_cross_log_integrable

#print axioms CatalanCore.Li2.Uniform.datum_negpart_uniform
#print axioms CatalanCore.Li2.Uniform.log_diff_le_negpart

#print axioms CatalanCore.Li2.Uniform.datum_holder_downgrade

#print axioms CatalanCore.Li2.Uniform.mixDatum_exists
#print axioms CatalanCore.Li2.Uniform.mixDatum_measure

#print axioms CatalanCore.Li2.Uniform.phi0_real_continuous
#print axioms CatalanCore.Li2.Uniform.W_real_continuous
#print axioms CatalanCore.Li2.Uniform.A_real_continuous

#print axioms CatalanCore.Li2.Uniform.W_real_tail_bound

#print axioms CatalanCore.Li2.Uniform.cap_integrable
