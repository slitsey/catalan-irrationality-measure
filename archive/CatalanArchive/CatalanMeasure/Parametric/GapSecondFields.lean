module
public import CatalanArchive.CatalanMeasure.Parametric.FlexibleSecondEnergy
public import CatalanArchive.CatalanMeasure.Parametric.GapBudgets
public import CatalanArchive.CatalanMeasure.Parametric.StrongNearField
public import CatalanArchive.CatalanMeasure.StrongTrial.Norms
public import CatalanArchive.CatalanMeasure.StrongTrial.First
public import CatalanArchive.CatalanMeasure.Cert.MarkedResidual
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan CatalanMeasure.Cert Set Filter
open scoped Topology
noncomputable section

private theorem gap_finite_near_of_first (pp : ℕ → ℝ) (hp : (9/50:ℝ) ≤ pp 1)
    {N : ℕ} (hN : 0<N) {y : ℝ} (hy : y ∈ Ioo (0:ℝ) 1) :
    -(9/10:ℝ)*Real.log (1+y^2)+((16*N-1:ℕ):ℝ)/(20*N)*Real.log y-
      pp 1*y ≤ -(3/4:ℝ) := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hd : (0:ℝ)<20*N := by positivity
  have hc : (3/4:ℝ) ≤ ((16*N-1:ℕ):ℝ)/(20*N) := by
    rw [le_div_iff₀ hd,Nat.cast_sub (by omega : 1 ≤ 16*N)]
    push_cast
    linarith only [hn]
  have hl : Real.log y ≤ 0 := Real.log_nonpos hy.1.le hy.2.le
  have hm := mul_le_mul_of_nonpos_right hc hl
  have hb := near_residual_field_le_three_fourths hp hy.1 hy.2.le
  linarith only [hm,hb]

/-- The three remaining uniform field certificates instantiate the complete
same-trial analytic contract. The norms and first coefficient are already checked. -/
def gapSecondTrialOfFields
    (hrow : ∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      shiftedRowField StrongTrial.R StrongTrial.Pc StrongTrial.Vc
        StrongTrial.P StrongTrial.V x ≤ (StrongTrial.MX:ℝ))
    (hcol : ∀ s ∈ Ioo (0:ℝ) 1,
      shiftedColumnField StrongTrial.C StrongTrial.Vc StrongTrial.V s ≤ (StrongTrial.MY:ℝ))
    (hres : ∀ x ∈ Icc (-1:ℝ) 1,
      (physicalAtomGap:ℝ) ≤ |x| → markedResidualField StrongTrial.Pc StrongTrial.P x ≤ gapResidualCap) :
    SecondTrialBoundsOn strongTarget gapResidualCap (-(3/4:ℝ)) gapSecondCost
      (fun x => (physicalAtomGap:ℝ) ≤ |x|) where
  p := trialSeq StrongTrial.Pc StrongTrial.P
  v := trialSeq StrongTrial.Vc StrongTrial.V
  MX := StrongTrial.MX
  MY := StrongTrial.MY
  normCap := strongNormSecond
  fieldCap := strongFieldsSecond
  p_summable := (trialSeq_summable (cs := StrongTrial.Pc) StrongTrial.tailsP).1
  v_summable := (trialSeq_summable (cs := StrongTrial.Vc) StrongTrial.tailsV).1
  norm_le := by
    convert StrongTrial.weighted_norm_le using 1 <;> norm_num [strongNormSecond]
  field_sum := by norm_num [StrongTrial.MX,StrongTrial.MY,strongFieldsSecond]
  row := by
    intro ε hε
    have hh := shiftedRowField_corrected_eventually StrongTrial.tailsP StrongTrial.tailsV
      (by decide +kernel : 0 ≤ StrongTrial.R.alpha)
      (by decide +kernel : 0<StrongTrial.R.beta)
      (a := 2) (b := 1/2) (by norm_num) (by norm_num) hrow
      TwentyCertified.reciprocalScale TwentyCertified.reciprocalScale_nonneg
      TwentyCertified.reciprocalScale_tendsto hε
    filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hc hN x hx
    rw [TwentyCertified.physicalTwo_row_identity]
    have hb := hc x hx
    rw [show StrongTrial.R=twentyRowWeights 2 0 by decide +kernel,
      twenty_shiftedRowField hN] at hb
    simpa only [Rat.cast_zero,Rat.cast_ofNat,zero_mul,add_zero] using hb
  column := by
    intro ε hε
    have hh := shiftedColumnField_corrected_eventually StrongTrial.tailsV
      (by decide +kernel : 0 ≤ StrongTrial.C.b)
      (by decide +kernel : 0<StrongTrial.C.q) hcol
      TwentyCertified.reciprocalScale TwentyCertified.reciprocalScale_nonneg
      TwentyCertified.reciprocalScale_tendsto hε
    filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hc hN s hs
    rw [TwentyCertified.physical_column_identity hN]
    have hb := hc s hs
    rw [show StrongTrial.C=twentyColumnWeights 0 by decide +kernel,
      twenty_shiftedColumnField] at hb
    simpa only [Rat.cast_zero,zero_mul,add_zero] using hb
  marked := by
    intro N hN x hx hgap
    have hn : (0:ℝ)<twenty.n N := by exact_mod_cast n_pos twenty_admissible hN
    have hsq : x^2 ≤ 1 := by nlinarith only [hx.1,hx.2]
    have hlog : Real.log (1+x^2) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) (by linarith only [hsq])
    have hcorr := div_le_div_of_nonneg_right hlog hn.le
    have hb := hres x hx hgap
    simp only [markedResidualField,zero_mul,neg_zero,zero_sub] at hb
    rw [twenty_grouped_marked_field_identity hN]
    linarith only [hb,hcorr]
  near := by
    intro N hN y hy
    have hn : (0:ℝ)<twenty.n N := by exact_mod_cast n_pos twenty_admissible hN
    have hsq : y^2 ≤ 1 := by nlinarith only [hy.1,hy.2]
    have hlog : Real.log (1+y^2) ≤ Real.log 2 :=
      Real.log_le_log (by positivity) (by linarith only [hsq])
    have hcorr := div_le_div_of_nonneg_right hlog hn.le
    have hb := gap_finite_near_of_first (trialSeq StrongTrial.Pc StrongTrial.P)
      StrongTrial.first_lower hN hy
    have he : twenty.n N-1-2*twenty.g N=16*N-1 := by
      change 20*N-1-2*(2*N)=16*N-1
      omega
    unfold groupedPhysicalNearField
    rw [twenty_grouped_marked_field_identity hN,he,abs_of_pos hy.1]
    have hnu : (twenty.n N:ℝ)=20*N := by simp [Parameters.n,twenty]
    rw [← hnu] at hb
    linarith only [hb,hcorr]
  budget := gap_second_budget

end
end CatalanMeasure.Parametric
