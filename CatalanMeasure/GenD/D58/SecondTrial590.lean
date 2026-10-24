module

public import CatalanMeasure.GenD.D58.Bank590
public import CatalanMeasure.GenD.D58.Cert590.XCover
public import CatalanMeasure.GenD.D58.Cert590.YCover
public import CatalanMeasure.GenD.D58.Cert590.RCover
public import CatalanMeasure.GenD.D58.Cert590.Norm
public import CatalanMeasure.GenD.D58.Cert590.Near

@[expose] public section

/-!
# D58 bank K590: the second-population hypotheses of `measure_590_of_certificates`

The frozen K590 witness `u = trialSeqS Pc P`, `v = trialSeqS Vc V` (`D58.Cert590.Data`) with the
certificates of `D58.Cert590` (block covers X, Y, R; the norm shards; the first coefficient):
summability, `MX + MY = K590.fieldCap`, `2 ‖u‖² + ‖v‖² / 2 ≤ K590.normCap`, the three field sups
(the residual one with the gap `g = 401/2500`) and the near-field inequality at the cap `-77/100`.
-/

namespace CatalanMeasure.GenD
namespace D58
open Set Filter CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.G728
open scoped Topology
noncomputable section

/-- the K590 second-population trial. -/
def secondU590 : ℕ → ℝ := trialSeqS Cert590.Pc Cert590.P
def secondV590 : ℕ → ℝ := trialSeqS Cert590.Vc Cert590.V

theorem second_hu590 : Summable (fun k => |secondU590 k|) := (trialSeqS_summable Cert590.tailsP).1
theorem second_hv590 : Summable (fun k => |secondV590 k|) := (trialSeqS_summable Cert590.tailsV).1

theorem second_field_sum590 :
    ((Cert590.MX : ℚ) : ℝ) + ((Cert590.MY : ℚ) : ℝ) = K590.fieldCap := by
  norm_num [Cert590.MX, Cert590.MY, K590.fieldCap]

theorem second_norm_le590 :
    2 * barrierTrialNormSq secondU590 + barrierTrialNormSq secondV590 / 2 ≤ K590.normCap := by
  have h := Cert590.weighted_norm_le
  have h2 : (((2 * Cert590.NP + Cert590.NV / 2 : ℚ)) : ℝ) ≤ K590.normCap := by
    norm_num [Cert590.NP, Cert590.NV, K590.normCap]
  unfold secondU590 secondV590
  linarith

theorem second_row_sup590 : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
    rowFieldG (11 / 29) (3 / 29) (39 / 29) secondU590 secondV590 x ≤ ((Cert590.MX : ℚ) : ℝ) := by
  intro x hx
  have h := Cert590.row_sup_S x hx
  have e : rowFieldS Cert590.R Cert590.Pc Cert590.Vc Cert590.P Cert590.V =
      rowFieldG (11 / 29) (3 / 29) (39 / 29) secondU590 secondV590 := by
    unfold rowFieldS secondU590 secondV590
    norm_num [Cert590.R]
  rw [e] at h
  exact h

theorem second_column_sup590 : ∀ s ∈ Ioo (0 : ℝ) 1,
    colFieldG (9 / 58) (3 / 58) secondV590 s ≤ ((Cert590.MY : ℚ) : ℝ) := by
  intro s hs
  have h := Cert590.column_sup_S s hs
  have e : colFieldS Cert590.C Cert590.Vc Cert590.V = colFieldG (9 / 58) (3 / 58) secondV590 := by
    unfold colFieldS secondV590
    norm_num [Cert590.C]
  rw [e] at h
  exact h

theorem second_residual_sup590 : ∀ x ∈ Icc (-1 : ℝ) 1, (401 / 2500 : ℝ) ≤ |x| →
    Analytic.resFieldGen (53 / 58) secondU590 x ≤ K590.residualCap := by
  intro x hx hg
  have h := Cert590.residual_sup_S x hx hg
  have e : Analytic.resFieldGen (53 / 58) secondU590 x =
      resFieldW (((53 / 58 : ℚ)) : ℝ) (trialSeqS Cert590.Pc Cert590.P) x := by
    unfold Analytic.resFieldGen resFieldW secondU590
    norm_num
  rw [e]
  have e2 : ((Cert590.MR : ℚ) : ℝ) = K590.residualCap := by norm_num [Cert590.MR, K590.residualCap]
  linarith

theorem second_near_sup_d58_590 : ∀ y ∈ Ioo (0 : ℝ) 1,
    -(53 / 58 : ℝ) * Real.log (1 + y ^ 2) + (47 / 58 : ℝ) * Real.log y - secondU590 1 * y ≤ -(77 / 100 : ℝ) :=
  fun y hy => Cert.near_residual_field_le_d58 Cert590.first_lower hy.1 hy.2.le

/-- Bank K590 with the second-population hypotheses of `measure_590_of_certificates` discharged
(gap `g = 401/2500`). -/
theorem measure_590_second_population_K590
    {rc C wc : ℝ} (hr1 : 1 < rc) (hr2 : rc ≤ 2)
    (hcirc : Analytic.GapCircleBound Odd.design (2 * (401 / 2500 : ℝ) / (1 + (401 / 2500 : ℝ) ^ 2)) rc C wc)
    (hwc : wc < K590.rho - 58 * K590.secondCost)
    (F : Analytic.FirstTrialBounds Odd.design K590.target K590.firstCost)
    (near_sup : ∀ y ∈ Ioo (0 : ℝ) 1,
      -Analytic.gRes Odd.design * Real.log (1 + y ^ 2) +
        (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) * Real.log y -
          secondU590 1 * y ≤ nearCap) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(590 : ℝ)) < |catalan - (a : ℝ) / b| :=
  measure_590_of_certificates_K590 (g := 401 / 2500) (by norm_num) (by norm_num) (by norm_num) hr1 hr2
    hcirc hwc F secondU590 secondV590 second_hu590 second_hv590 (Cert590.MX : ℚ) (Cert590.MY : ℚ)
    second_field_sum590 second_norm_le590 near_sup second_row_sup590 second_column_sup590
    second_residual_sup590

end
end D58
end CatalanMeasure.GenD
#print axioms CatalanMeasure.GenD.D58.measure_590_second_population_K590
