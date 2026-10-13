module
public import CatalanMeasure.Parametric.TwentyFixedOneFields
public import CatalanMeasure.Cert.ShiftedStability
public import Mathlib.Analysis.SpecificLimits.Basic
@[expose] public section
namespace CatalanMeasure.Parametric.TwentyCertified
open OAI.InternalCatalan CatalanMeasure.Cert Set Filter
open scoped Topology
noncomputable section

def reciprocalScale (N : ℕ) : ℝ :=1/(20*(N:ℝ))
theorem reciprocalScale_nonneg (N : ℕ) : 0 ≤ reciprocalScale N :=by
  unfold reciprocalScale
  positivity
theorem reciprocalScale_tendsto : Tendsto reciprocalScale atTop (𝓝 0) :=by
  unfold reciprocalScale
  simpa only [div_div] using
    (tendsto_const_div_atTop_nhds_zero_nat (1/20:ℝ))
theorem tailP10 : tailsInDisk CatalanMeasure.TwentyTrial.K1A0.P=true :=by decide +kernel
theorem tailV10 : tailsInDisk CatalanMeasure.TwentyTrial.K1A0.V=true :=by decide +kernel
theorem p10_summable : Summable (fun j =>|p10 j|) :=by
  have hs :=(trialSeq_summable (cs :=CatalanMeasure.TwentyTrial.K1A0.Pc) tailP10).1
  simpa only [p10,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] using hs.mul_left (2:ℝ)
theorem v10_summable : Summable (fun j =>|v10 j|) :=
  (trialSeq_summable (cs :=CatalanMeasure.TwentyTrial.K1A0.Vc) tailV10).1

theorem row10_corrected_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      paramPopulationRowField twenty N 1 x+(lambda10:ℝ)*paramCaseField twenty N x-
        2*barrierTrialT p10 x-barrierTrialS v10 x+
        reciprocalScale N*(3/2*Real.log (1+x^2)-(1/2)*Real.log (1-x)) ≤
        (CatalanMeasure.TwentyTrial.K1A0.MX:ℝ)+ε :=by
  have hh :=shiftedRowField_corrected_eventually tailP10 tailV10
    (by decide +kernel : 0 ≤ CatalanMeasure.TwentyTrial.K1A0.R.alpha) (by decide +kernel : 0<CatalanMeasure.TwentyTrial.K1A0.R.beta)
    (a :=3/2) (b :=1/2) (by norm_num) (by norm_num)
    CatalanMeasure.TwentyTrial.K1A0.row_sup reciprocalScale reciprocalScale_nonneg reciprocalScale_tendsto hε
  filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hc hN x hx
  have hp :=hc x hx
  rw [rowWeights10,twenty_shiftedFirstRowField hN] at hp
  exact hp

theorem column10_corrected_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ s ∈ Ioo (0:ℝ) 1,
      (3/20:ℝ)*Real.log s+(1/20:ℝ)*Real.log (1-s)+(0:ℝ)*Real.log (1+s)+
        2*barrierTrialT v10 s-reciprocalScale N*Real.log (1-s) ≤ (CatalanMeasure.TwentyTrial.K1A0.MY:ℝ)+ε :=by
  have hh :=shiftedColumnField_corrected_eventually tailV10
    (by decide +kernel : 0 ≤ CatalanMeasure.TwentyTrial.K1A0.C.b) (by decide +kernel : 0<CatalanMeasure.TwentyTrial.K1A0.C.q)
    CatalanMeasure.TwentyTrial.K1A0.column_sup reciprocalScale reciprocalScale_nonneg reciprocalScale_tendsto hε
  filter_upwards [hh] with N hc s hs
  have hp :=hc s hs
  rw [columnWeights10,twenty_shiftedColumnField] at hp
  simpa only [Rat.cast_zero,Rat.cast_one,v10] using hp
theorem tailP11 : tailsInDisk CatalanMeasure.TwentyTrial.K1A1.P=true :=by decide +kernel
theorem tailV11 : tailsInDisk CatalanMeasure.TwentyTrial.K1A1.V=true :=by decide +kernel
theorem p11_summable : Summable (fun j =>|p11 j|) :=by
  have hs :=(trialSeq_summable (cs :=CatalanMeasure.TwentyTrial.K1A1.Pc) tailP11).1
  simpa only [p11,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] using hs.mul_left (2:ℝ)
theorem v11_summable : Summable (fun j =>|v11 j|) :=
  (trialSeq_summable (cs :=CatalanMeasure.TwentyTrial.K1A1.Vc) tailV11).1

theorem row11_corrected_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      paramPopulationRowField twenty N 1 x+(lambda11:ℝ)*paramCaseField twenty N x-
        2*barrierTrialT p11 x-barrierTrialS v11 x+
        reciprocalScale N*(3/2*Real.log (1+x^2)-(1/2)*Real.log (1-x)) ≤
        (CatalanMeasure.TwentyTrial.K1A1.MX:ℝ)+ε :=by
  have hh :=shiftedRowField_corrected_eventually tailP11 tailV11
    (by decide +kernel : 0 ≤ CatalanMeasure.TwentyTrial.K1A1.R.alpha) (by decide +kernel : 0<CatalanMeasure.TwentyTrial.K1A1.R.beta)
    (a :=3/2) (b :=1/2) (by norm_num) (by norm_num)
    CatalanMeasure.TwentyTrial.K1A1.row_sup reciprocalScale reciprocalScale_nonneg reciprocalScale_tendsto hε
  filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hc hN x hx
  have hp :=hc x hx
  rw [rowWeights11,twenty_shiftedFirstRowField hN] at hp
  exact hp

theorem column11_corrected_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ s ∈ Ioo (0:ℝ) 1,
      (3/20:ℝ)*Real.log s+(1/20:ℝ)*Real.log (1-s)+(1:ℝ)*Real.log (1+s)+
        2*barrierTrialT v11 s-reciprocalScale N*Real.log (1-s) ≤ (CatalanMeasure.TwentyTrial.K1A1.MY:ℝ)+ε :=by
  have hh :=shiftedColumnField_corrected_eventually tailV11
    (by decide +kernel : 0 ≤ CatalanMeasure.TwentyTrial.K1A1.C.b) (by decide +kernel : 0<CatalanMeasure.TwentyTrial.K1A1.C.q)
    CatalanMeasure.TwentyTrial.K1A1.column_sup reciprocalScale reciprocalScale_nonneg reciprocalScale_tendsto hε
  filter_upwards [hh] with N hc s hs
  have hp :=hc s hs
  rw [columnWeights11,twenty_shiftedColumnField] at hp
  simpa only [Rat.cast_zero,Rat.cast_one,v11] using hp
theorem tailP20 : tailsInDisk CatalanMeasure.TwentyTrial.K2A0.P=true :=by decide +kernel
theorem tailV20 : tailsInDisk CatalanMeasure.TwentyTrial.K2A0.V=true :=by decide +kernel
theorem p20_summable : Summable (fun j =>|p20 j|) :=by
  have hs :=(trialSeq_summable (cs :=CatalanMeasure.TwentyTrial.K2A0.Pc) tailP20).1
  exact hs
theorem v20_summable : Summable (fun j =>|v20 j|) :=
  (trialSeq_summable (cs :=CatalanMeasure.TwentyTrial.K2A0.Vc) tailV20).1

theorem row20_corrected_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      paramPopulationRowField twenty N 2 x+(lambda20:ℝ)*paramCaseField twenty N x-
        4*barrierTrialT p20 x-barrierTrialS v20 x+
        reciprocalScale N*(2*Real.log (1+x^2)-(1/2)*Real.log (1-x)) ≤
        (CatalanMeasure.TwentyTrial.K2A0.MX:ℝ)+ε :=by
  have hh :=shiftedRowField_corrected_eventually tailP20 tailV20
    (by decide +kernel : 0 ≤ CatalanMeasure.TwentyTrial.K2A0.R.alpha) (by decide +kernel : 0<CatalanMeasure.TwentyTrial.K2A0.R.beta)
    (a :=2) (b :=1/2) (by norm_num) (by norm_num)
    CatalanMeasure.TwentyTrial.K2A0.row_sup reciprocalScale reciprocalScale_nonneg reciprocalScale_tendsto hε
  filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hc hN x hx
  have hp :=hc x hx
  rw [rowWeights20,twenty_shiftedRowField hN] at hp
  exact hp

theorem column20_corrected_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ s ∈ Ioo (0:ℝ) 1,
      (3/20:ℝ)*Real.log s+(1/20:ℝ)*Real.log (1-s)+(0:ℝ)*Real.log (1+s)+
        2*barrierTrialT v20 s-reciprocalScale N*Real.log (1-s) ≤ (CatalanMeasure.TwentyTrial.K2A0.MY:ℝ)+ε :=by
  have hh :=shiftedColumnField_corrected_eventually tailV20
    (by decide +kernel : 0 ≤ CatalanMeasure.TwentyTrial.K2A0.C.b) (by decide +kernel : 0<CatalanMeasure.TwentyTrial.K2A0.C.q)
    CatalanMeasure.TwentyTrial.K2A0.column_sup reciprocalScale reciprocalScale_nonneg reciprocalScale_tendsto hε
  filter_upwards [hh] with N hc s hs
  have hp :=hc s hs
  rw [columnWeights20,twenty_shiftedColumnField] at hp
  simpa only [Rat.cast_zero,Rat.cast_one,v20] using hp
theorem tailP21 : tailsInDisk CatalanMeasure.TwentyTrial.K2A1.P=true :=by decide +kernel
theorem tailV21 : tailsInDisk CatalanMeasure.TwentyTrial.K2A1.V=true :=by decide +kernel
theorem p21_summable : Summable (fun j =>|p21 j|) :=by
  have hs :=(trialSeq_summable (cs :=CatalanMeasure.TwentyTrial.K2A1.Pc) tailP21).1
  exact hs
theorem v21_summable : Summable (fun j =>|v21 j|) :=
  (trialSeq_summable (cs :=CatalanMeasure.TwentyTrial.K2A1.Vc) tailV21).1

theorem row21_corrected_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      paramPopulationRowField twenty N 2 x+(lambda21:ℝ)*paramCaseField twenty N x-
        4*barrierTrialT p21 x-barrierTrialS v21 x+
        reciprocalScale N*(2*Real.log (1+x^2)-(1/2)*Real.log (1-x)) ≤
        (CatalanMeasure.TwentyTrial.K2A1.MX:ℝ)+ε :=by
  have hh :=shiftedRowField_corrected_eventually tailP21 tailV21
    (by decide +kernel : 0 ≤ CatalanMeasure.TwentyTrial.K2A1.R.alpha) (by decide +kernel : 0<CatalanMeasure.TwentyTrial.K2A1.R.beta)
    (a :=2) (b :=1/2) (by norm_num) (by norm_num)
    CatalanMeasure.TwentyTrial.K2A1.row_sup reciprocalScale reciprocalScale_nonneg reciprocalScale_tendsto hε
  filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hc hN x hx
  have hp :=hc x hx
  rw [rowWeights21,twenty_shiftedRowField hN] at hp
  exact hp

theorem column21_corrected_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,∀ s ∈ Ioo (0:ℝ) 1,
      (3/20:ℝ)*Real.log s+(1/20:ℝ)*Real.log (1-s)+(1:ℝ)*Real.log (1+s)+
        2*barrierTrialT v21 s-reciprocalScale N*Real.log (1-s) ≤ (CatalanMeasure.TwentyTrial.K2A1.MY:ℝ)+ε :=by
  have hh :=shiftedColumnField_corrected_eventually tailV21
    (by decide +kernel : 0 ≤ CatalanMeasure.TwentyTrial.K2A1.C.b) (by decide +kernel : 0<CatalanMeasure.TwentyTrial.K2A1.C.q)
    CatalanMeasure.TwentyTrial.K2A1.column_sup reciprocalScale reciprocalScale_nonneg reciprocalScale_tendsto hε
  filter_upwards [hh] with N hc s hs
  have hp :=hc s hs
  rw [columnWeights21,twenty_shiftedColumnField] at hp
  simpa only [Rat.cast_zero,Rat.cast_one,v21] using hp

end
end CatalanMeasure.Parametric.TwentyCertified
