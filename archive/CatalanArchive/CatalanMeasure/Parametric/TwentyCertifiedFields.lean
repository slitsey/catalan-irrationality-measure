module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyCertificatesAudit
public import CatalanArchive.CatalanMeasure.Parametric.TwentyTrialFields
public import CatalanArchive.CatalanMeasure.Parametric.TwentyFixedFields
public import CatalanArchive.CatalanMeasure.Parametric.TwentyBudgets
@[expose] public section
namespace CatalanMeasure.Parametric.TwentyCertified
open OAI.InternalCatalan CatalanMeasure.Cert Set
noncomputable section
def lambda10 : ℚ :=229193331/100000000
def p10 (j : ℕ) : ℝ :=2*trialSeq CatalanMeasure.TwentyTrial.K1A0.Pc CatalanMeasure.TwentyTrial.K1A0.P j
def v10 : ℕ → ℝ :=trialSeq CatalanMeasure.TwentyTrial.K1A0.Vc CatalanMeasure.TwentyTrial.K1A0.V
theorem rowWeights10 : CatalanMeasure.TwentyTrial.K1A0.R=twentyRowWeights 1 lambda10 :=by decide +kernel
theorem columnWeights10 : CatalanMeasure.TwentyTrial.K1A0.C=twentyColumnWeights 0 :=by decide +kernel
theorem row10_bound {N : ℕ} (hN : 0<N) {x : ℝ}
    (hx : x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1) :
    paramPopulationRowField twenty N 1 x+(lambda10:ℝ)*paramCaseField twenty N x-
      2*barrierTrialT p10 x-barrierTrialS v10 x ≤ (CatalanMeasure.TwentyTrial.K1A0.MX:ℝ) :=by
  have hh : shiftedRowField (twentyRowWeights 1 lambda10) CatalanMeasure.TwentyTrial.K1A0.Pc CatalanMeasure.TwentyTrial.K1A0.Vc CatalanMeasure.TwentyTrial.K1A0.P CatalanMeasure.TwentyTrial.K1A0.V x ≤ (CatalanMeasure.TwentyTrial.K1A0.MX:ℝ) :=by
    rw [← rowWeights10]
    exact CatalanMeasure.TwentyTrial.K1A0.row_sup x hx
  rw [twenty_shiftedFirstRowField hN] at hh
  exact hh

theorem column10_bound {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    (3/20:ℝ)*Real.log s+(1/20:ℝ)*Real.log (1-s)+(0:ℝ)*Real.log (1+s)+
      2*barrierTrialT v10 s ≤ (CatalanMeasure.TwentyTrial.K1A0.MY:ℝ) :=by
  have hh : shiftedColumnField (twentyColumnWeights 0) CatalanMeasure.TwentyTrial.K1A0.Vc CatalanMeasure.TwentyTrial.K1A0.V s ≤ (CatalanMeasure.TwentyTrial.K1A0.MY:ℝ) :=by
    rw [← columnWeights10]
    exact CatalanMeasure.TwentyTrial.K1A0.column_sup s hs
  rw [twenty_shiftedColumnField] at hh
  simpa only [Rat.cast_zero,Rat.cast_one,v10] using hh

theorem norm10_bound : 1*barrierTrialNormSq p10+barrierTrialNormSq v10/2 ≤ twentyNorm10 :=by
  have hp := CatalanMeasure.TwentyTrial.K1A0.normP_le
  have hv := CatalanMeasure.TwentyTrial.K1A0.normV_le
  unfold p10 v10
  rw [population_trialNormSq_mul]
  norm_num [CatalanMeasure.TwentyTrial.K1A0.NP,CatalanMeasure.TwentyTrial.K1A0.NV] at hp hv
  unfold twentyNorm10
  nlinarith only [hp,hv]

theorem fieldSum10 : (CatalanMeasure.TwentyTrial.K1A0.MX:ℝ)+(CatalanMeasure.TwentyTrial.K1A0.MY:ℝ)=twentyFields10 :=by
  norm_num [CatalanMeasure.TwentyTrial.K1A0.MX,CatalanMeasure.TwentyTrial.K1A0.MY,twentyFields10]
def lambda11 : ℚ :=120853833/50000000
def p11 (j : ℕ) : ℝ :=2*trialSeq CatalanMeasure.TwentyTrial.K1A1.Pc CatalanMeasure.TwentyTrial.K1A1.P j
def v11 : ℕ → ℝ :=trialSeq CatalanMeasure.TwentyTrial.K1A1.Vc CatalanMeasure.TwentyTrial.K1A1.V
theorem rowWeights11 : CatalanMeasure.TwentyTrial.K1A1.R=twentyRowWeights 1 lambda11 :=by decide +kernel
theorem columnWeights11 : CatalanMeasure.TwentyTrial.K1A1.C=twentyColumnWeights 1 :=by decide +kernel
theorem row11_bound {N : ℕ} (hN : 0<N) {x : ℝ}
    (hx : x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1) :
    paramPopulationRowField twenty N 1 x+(lambda11:ℝ)*paramCaseField twenty N x-
      2*barrierTrialT p11 x-barrierTrialS v11 x ≤ (CatalanMeasure.TwentyTrial.K1A1.MX:ℝ) :=by
  have hh : shiftedRowField (twentyRowWeights 1 lambda11) CatalanMeasure.TwentyTrial.K1A1.Pc CatalanMeasure.TwentyTrial.K1A1.Vc CatalanMeasure.TwentyTrial.K1A1.P CatalanMeasure.TwentyTrial.K1A1.V x ≤ (CatalanMeasure.TwentyTrial.K1A1.MX:ℝ) :=by
    rw [← rowWeights11]
    exact CatalanMeasure.TwentyTrial.K1A1.row_sup x hx
  rw [twenty_shiftedFirstRowField hN] at hh
  exact hh

theorem column11_bound {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    (3/20:ℝ)*Real.log s+(1/20:ℝ)*Real.log (1-s)+(1:ℝ)*Real.log (1+s)+
      2*barrierTrialT v11 s ≤ (CatalanMeasure.TwentyTrial.K1A1.MY:ℝ) :=by
  have hh : shiftedColumnField (twentyColumnWeights 1) CatalanMeasure.TwentyTrial.K1A1.Vc CatalanMeasure.TwentyTrial.K1A1.V s ≤ (CatalanMeasure.TwentyTrial.K1A1.MY:ℝ) :=by
    rw [← columnWeights11]
    exact CatalanMeasure.TwentyTrial.K1A1.column_sup s hs
  rw [twenty_shiftedColumnField] at hh
  simpa only [Rat.cast_zero,Rat.cast_one,v11] using hh

theorem norm11_bound : 1*barrierTrialNormSq p11+barrierTrialNormSq v11/2 ≤ twentyNorm11 :=by
  have hp := CatalanMeasure.TwentyTrial.K1A1.normP_le
  have hv := CatalanMeasure.TwentyTrial.K1A1.normV_le
  unfold p11 v11
  rw [population_trialNormSq_mul]
  norm_num [CatalanMeasure.TwentyTrial.K1A1.NP,CatalanMeasure.TwentyTrial.K1A1.NV] at hp hv
  unfold twentyNorm11
  nlinarith only [hp,hv]

theorem fieldSum11 : (CatalanMeasure.TwentyTrial.K1A1.MX:ℝ)+(CatalanMeasure.TwentyTrial.K1A1.MY:ℝ)=twentyFields11 :=by
  norm_num [CatalanMeasure.TwentyTrial.K1A1.MX,CatalanMeasure.TwentyTrial.K1A1.MY,twentyFields11]
def lambda20 : ℚ :=0
def p20 (j : ℕ) : ℝ :=trialSeq CatalanMeasure.TwentyTrial.K2A0.Pc CatalanMeasure.TwentyTrial.K2A0.P j
def v20 : ℕ → ℝ :=trialSeq CatalanMeasure.TwentyTrial.K2A0.Vc CatalanMeasure.TwentyTrial.K2A0.V
theorem rowWeights20 : CatalanMeasure.TwentyTrial.K2A0.R=twentyRowWeights 2 lambda20 :=by decide +kernel
theorem columnWeights20 : CatalanMeasure.TwentyTrial.K2A0.C=twentyColumnWeights 0 :=by decide +kernel
theorem row20_bound {N : ℕ} (hN : 0<N) {x : ℝ}
    (hx : x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1) :
    paramPopulationRowField twenty N 2 x+(lambda20:ℝ)*paramCaseField twenty N x-
      4*barrierTrialT p20 x-barrierTrialS v20 x ≤ (CatalanMeasure.TwentyTrial.K2A0.MX:ℝ) :=by
  have hh : shiftedRowField (twentyRowWeights 2 lambda20) CatalanMeasure.TwentyTrial.K2A0.Pc CatalanMeasure.TwentyTrial.K2A0.Vc CatalanMeasure.TwentyTrial.K2A0.P CatalanMeasure.TwentyTrial.K2A0.V x ≤ (CatalanMeasure.TwentyTrial.K2A0.MX:ℝ) :=by
    rw [← rowWeights20]
    exact CatalanMeasure.TwentyTrial.K2A0.row_sup x hx
  rw [twenty_shiftedRowField hN] at hh
  exact hh

theorem column20_bound {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    (3/20:ℝ)*Real.log s+(1/20:ℝ)*Real.log (1-s)+(0:ℝ)*Real.log (1+s)+
      2*barrierTrialT v20 s ≤ (CatalanMeasure.TwentyTrial.K2A0.MY:ℝ) :=by
  have hh : shiftedColumnField (twentyColumnWeights 0) CatalanMeasure.TwentyTrial.K2A0.Vc CatalanMeasure.TwentyTrial.K2A0.V s ≤ (CatalanMeasure.TwentyTrial.K2A0.MY:ℝ) :=by
    rw [← columnWeights20]
    exact CatalanMeasure.TwentyTrial.K2A0.column_sup s hs
  rw [twenty_shiftedColumnField] at hh
  simpa only [Rat.cast_zero,Rat.cast_one,v20] using hh

theorem norm20_bound : 2*barrierTrialNormSq p20+barrierTrialNormSq v20/2 ≤ twentyNorm20 :=by
  have hp := CatalanMeasure.TwentyTrial.K2A0.normP_le
  have hv := CatalanMeasure.TwentyTrial.K2A0.normV_le
  unfold p20 v20
  norm_num [CatalanMeasure.TwentyTrial.K2A0.NP,CatalanMeasure.TwentyTrial.K2A0.NV] at hp hv
  unfold twentyNorm20
  nlinarith only [hp,hv]

theorem fieldSum20 : (CatalanMeasure.TwentyTrial.K2A0.MX:ℝ)+(CatalanMeasure.TwentyTrial.K2A0.MY:ℝ)=twentyFields20 :=by
  norm_num [CatalanMeasure.TwentyTrial.K2A0.MX,CatalanMeasure.TwentyTrial.K2A0.MY,twentyFields20]
theorem residualPc20 : CatalanMeasure.TwentyResidualFixed0.Pc=CatalanMeasure.TwentyTrial.K2A0.Pc :=by decide +kernel
theorem residualP20 : CatalanMeasure.TwentyResidualFixed0.P=CatalanMeasure.TwentyTrial.K2A0.P :=by decide +kernel
theorem fixed20_bound {N : ℕ} (hN : 0<N) {x : ℝ} (hx0 : -1≤x) (hx : x<0) :
    paramPopulationRowField twenty N 2 x-2*barrierTrialT p20 x-
      Real.log |(rowCommonFactor twenty N).eval (realCoordinateInv x)|/(twenty.n N:ℝ) ≤ -(1/5:ℝ) :=by
  unfold p20
  rw [twenty_fixed_two_after_common hN _ _ hx]
  rw [← residualPc20,← residualP20]
  exact CatalanMeasure.TwentyResidualFixed0.actual_fixed_field_sup x ⟨hx0,hx.le⟩
def lambda21 : ℚ :=0
def p21 (j : ℕ) : ℝ :=trialSeq CatalanMeasure.TwentyTrial.K2A1.Pc CatalanMeasure.TwentyTrial.K2A1.P j
def v21 : ℕ → ℝ :=trialSeq CatalanMeasure.TwentyTrial.K2A1.Vc CatalanMeasure.TwentyTrial.K2A1.V
theorem rowWeights21 : CatalanMeasure.TwentyTrial.K2A1.R=twentyRowWeights 2 lambda21 :=by decide +kernel
theorem columnWeights21 : CatalanMeasure.TwentyTrial.K2A1.C=twentyColumnWeights 1 :=by decide +kernel
theorem row21_bound {N : ℕ} (hN : 0<N) {x : ℝ}
    (hx : x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1) :
    paramPopulationRowField twenty N 2 x+(lambda21:ℝ)*paramCaseField twenty N x-
      4*barrierTrialT p21 x-barrierTrialS v21 x ≤ (CatalanMeasure.TwentyTrial.K2A1.MX:ℝ) :=by
  have hh : shiftedRowField (twentyRowWeights 2 lambda21) CatalanMeasure.TwentyTrial.K2A1.Pc CatalanMeasure.TwentyTrial.K2A1.Vc CatalanMeasure.TwentyTrial.K2A1.P CatalanMeasure.TwentyTrial.K2A1.V x ≤ (CatalanMeasure.TwentyTrial.K2A1.MX:ℝ) :=by
    rw [← rowWeights21]
    exact CatalanMeasure.TwentyTrial.K2A1.row_sup x hx
  rw [twenty_shiftedRowField hN] at hh
  exact hh

theorem column21_bound {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    (3/20:ℝ)*Real.log s+(1/20:ℝ)*Real.log (1-s)+(1:ℝ)*Real.log (1+s)+
      2*barrierTrialT v21 s ≤ (CatalanMeasure.TwentyTrial.K2A1.MY:ℝ) :=by
  have hh : shiftedColumnField (twentyColumnWeights 1) CatalanMeasure.TwentyTrial.K2A1.Vc CatalanMeasure.TwentyTrial.K2A1.V s ≤ (CatalanMeasure.TwentyTrial.K2A1.MY:ℝ) :=by
    rw [← columnWeights21]
    exact CatalanMeasure.TwentyTrial.K2A1.column_sup s hs
  rw [twenty_shiftedColumnField] at hh
  simpa only [Rat.cast_zero,Rat.cast_one,v21] using hh

theorem norm21_bound : 2*barrierTrialNormSq p21+barrierTrialNormSq v21/2 ≤ twentyNorm21 :=by
  have hp := CatalanMeasure.TwentyTrial.K2A1.normP_le
  have hv := CatalanMeasure.TwentyTrial.K2A1.normV_le
  unfold p21 v21
  norm_num [CatalanMeasure.TwentyTrial.K2A1.NP,CatalanMeasure.TwentyTrial.K2A1.NV] at hp hv
  unfold twentyNorm21
  nlinarith only [hp,hv]

theorem fieldSum21 : (CatalanMeasure.TwentyTrial.K2A1.MX:ℝ)+(CatalanMeasure.TwentyTrial.K2A1.MY:ℝ)=twentyFields21 :=by
  norm_num [CatalanMeasure.TwentyTrial.K2A1.MX,CatalanMeasure.TwentyTrial.K2A1.MY,twentyFields21]
theorem residualPc21 : CatalanMeasure.TwentyResidualFixed1.Pc=CatalanMeasure.TwentyTrial.K2A1.Pc :=by decide +kernel
theorem residualP21 : CatalanMeasure.TwentyResidualFixed1.P=CatalanMeasure.TwentyTrial.K2A1.P :=by decide +kernel
theorem fixed21_bound {N : ℕ} (hN : 0<N) {x : ℝ} (hx0 : -1≤x) (hx : x<0) :
    paramPopulationRowField twenty N 2 x-2*barrierTrialT p21 x-
      Real.log |(rowCommonFactor twenty N).eval (realCoordinateInv x)|/(twenty.n N:ℝ) ≤ -(1/5:ℝ) :=by
  unfold p21
  rw [twenty_fixed_two_after_common hN _ _ hx]
  rw [← residualPc21,← residualP21]
  exact CatalanMeasure.TwentyResidualFixed1.actual_fixed_field_sup x ⟨hx0,hx.le⟩

end
end CatalanMeasure.Parametric.TwentyCertified
