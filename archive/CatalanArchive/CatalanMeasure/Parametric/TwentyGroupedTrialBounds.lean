module

public import CatalanArchive.CatalanMeasure.Parametric.TwentyCertifiedFields
public import CatalanArchive.CatalanMeasure.Parametric.NearResidualCap
public import CatalanArchive.CatalanMeasure.TwentyMarkedPositiveCertificate
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Published trial bounds for full-interval actual and near marked populations

The positive residual cover supplements the existing negative cover. The first
trial coefficient is checked from the exact published rational data.
-/

@[expose] public section

namespace CatalanMeasure.Parametric.TwentyCertified

open OAI.InternalCatalan CatalanMeasure.Cert Set

noncomputable section

theorem p20_first_lower : (9 / 50 : ℝ) ≤ p20 1 := by
  norm_num [p20, trialSeq, barrierTrial, barrierFiniteCoeff,
    CatalanMeasure.TwentyTrial.K2A0.Pc, CatalanMeasure.TwentyTrial.K2A0.P,
    TailQ.toC, barrierComplex, Complex.mul_re]

theorem grouped_marked_field_bound {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    -(9 / 10 : ℝ) * Real.log (1 + x ^ 2) - 2 * barrierTrialT p20 x ≤ (2 / 25 : ℝ) := by
  have hres : residualTwoField CatalanMeasure.TwentyResidualFixed0.Pc
      CatalanMeasure.TwentyResidualFixed0.P x ≤ -(101 / 500 : ℝ) := by
    by_cases hneg : x ≤ 0
    · exact CatalanMeasure.TwentyResidualFixed0.field_sup x ⟨hx.1,hneg⟩
    · exact CatalanMeasure.TwentyMarkedPositive.field_sup x ⟨(le_of_not_ge hneg),hx.2⟩
  change -(3 / 8 : ℝ) * Real.log 2 - (89 / 96 : ℝ) * Real.log (1 + x ^ 2) -
    2 * barrierTrialT p20 x ≤ -(101 / 500 : ℝ) at hres
  have hsq : x ^ 2 ≤ 1 := by nlinarith only [hx.1,hx.2]
  have hlog : Real.log (1 + x ^ 2) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) (by linarith only [hsq])
  have hu := Real.log_two_lt_d9
  norm_num at hu
  linarith only [hres,hlog,hu]

theorem grouped_near_field_bound {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    -(9 / 10 : ℝ) * Real.log (1 + y ^ 2) + (4 / 5 : ℝ) * Real.log y - p20 1 * y ≤
      -(63 / 100 : ℝ) :=
  near_residual_field_le p20_first_lower hy.1 hy.2.le

end

end CatalanMeasure.Parametric.TwentyCertified
