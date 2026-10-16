module
public import CatalanMeasure.Parametric.FlexibleFirstEnergy
public import CatalanMeasure.FirstStrongTrial.Norms
public import CatalanMeasure.FirstStrongTrial.First
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan CatalanMeasure.Cert Set Filter
open scoped Topology
noncomputable section

/-- The frozen new first trial enters the physical energy argument only through
its own checked norm, row and column fields. -/
def strongFirstTrialOfFields
    (hrow : ∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      shiftedRowField FirstStrongTrial.R FirstStrongTrial.Pc FirstStrongTrial.Vc
        FirstStrongTrial.P FirstStrongTrial.V x ≤ (FirstStrongTrial.MX:ℝ))
    (hcol : ∀ s ∈ Ioo (0:ℝ) 1,
      shiftedColumnField FirstStrongTrial.C FirstStrongTrial.Vc FirstStrongTrial.V s ≤
        (FirstStrongTrial.MY:ℝ)) : FirstTrialBoundsAt strongTarget strongFirstCost where
  p := FirstStrongTrial.physicalP
  v := FirstStrongTrial.physicalV
  lambda := strongLambda
  MX := FirstStrongTrial.MX
  MY := FirstStrongTrial.MY
  normCap := strongNormFirst
  fieldCap := strongFieldsFirst
  lambda_nonneg := by norm_num [strongLambda]
  p_summable := by
    have hs := (trialSeq_summable (cs := FirstStrongTrial.Pc) FirstStrongTrial.tailsP).1
    simpa only [FirstStrongTrial.physicalP,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      using hs.mul_left (2:ℝ)
  v_summable := (trialSeq_summable (cs := FirstStrongTrial.Vc) FirstStrongTrial.tailsV).1
  norm_le := FirstStrongTrial.physical_norm_le
  field_sum := by norm_num [FirstStrongTrial.MX,FirstStrongTrial.MY,strongFieldsFirst]
  row := by
    intro ε hε
    have hh := shiftedRowField_corrected_eventually FirstStrongTrial.tailsP FirstStrongTrial.tailsV
      (by decide +kernel : 0≤FirstStrongTrial.R.alpha)
      (by decide +kernel : 0<FirstStrongTrial.R.beta)
      (a := 3/2) (b := 1/2) (by norm_num) (by norm_num) hrow
      TwentyCertified.reciprocalScale TwentyCertified.reciprocalScale_nonneg
      TwentyCertified.reciprocalScale_tendsto hε
    filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hc hN x hx
    rw [TwentyCertified.physicalOne_row_identity]
    have hb := hc x hx
    rw [show FirstStrongTrial.R=twentyRowWeights 1 (168493357/100000000) by decide +kernel,
      twenty_shiftedFirstRowField hN] at hb
    have hp : (fun j => 2*trialSeq FirstStrongTrial.Pc FirstStrongTrial.P j)=
        FirstStrongTrial.physicalP := rfl
    rw [hp] at hb
    simpa only [FirstStrongTrial.physicalV,strongLambda,
      Rat.cast_div,Rat.cast_ofNat] using hb
  column := by
    intro ε hε
    have hh := shiftedColumnField_corrected_eventually FirstStrongTrial.tailsV
      (by decide +kernel : 0≤FirstStrongTrial.C.b)
      (by decide +kernel : 0<FirstStrongTrial.C.q) hcol
      TwentyCertified.reciprocalScale TwentyCertified.reciprocalScale_nonneg
      TwentyCertified.reciprocalScale_tendsto hε
    filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hc hN s hs
    rw [TwentyCertified.physical_column_identity hN]
    have hb := hc s hs
    rw [show FirstStrongTrial.C=twentyColumnWeights 0 by decide +kernel,
      twenty_shiftedColumnField] at hb
    simpa only [FirstStrongTrial.physicalV,Rat.cast_zero,zero_mul,add_zero] using hb
  budget := strong_first_budget

end
end CatalanMeasure.Parametric
