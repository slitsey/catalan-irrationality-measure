module

public import CatalanMeasure.GenD.D58.Certified
public import CatalanMeasure.GenD.D58.Cert.XCover
public import CatalanMeasure.GenD.D58.Cert.YCover
public import CatalanMeasure.GenD.D58.Cert.RCover
public import CatalanMeasure.GenD.D58.Cert.Norm
public import CatalanMeasure.GenD.D58.Cert.Near

@[expose] public section

/-!
# D58 bank K160: the second-population hypotheses of `measure_592_of_certificates`

The frozen K160 witness `u = trialSeqS Pc P`, `v = trialSeqS Vc V` (`D58.Cert.Data`) with the
certificates of `D58.Cert` (block covers X, Y, R; the norm shards; the near-field inequality):

* `second_hu`, `second_hv`        summability,
* `second_field_sum`              `MX + MY = K160.fieldCap`,
* `second_norm_le`                `2 ‖u‖² + ‖v‖² / 2 ≤ K160.normCap`,
* `second_row_sup`, `second_column_sup`, `second_residual_sup` the three sups
  (the residual one with the gap `g = 401/2500`),
* `second_near_sup_d58`           the near-field inequality with the cap `-77/100`.

The near cap `D58.nearCap = -39/50` is not valid for the weight `47/58`: the supremum is about
`-0.7758 > -0.78` (see `Cert.Near`).  `measure_592_of_certificates` needs `near_sup` with
`nearCap`; the cap `-77/100` satisfies the budget gate `hi - residualCap + nearCap ≤ 0`.
-/

namespace CatalanMeasure.GenD
namespace D58
open Set Filter CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.G728
open scoped Topology
noncomputable section

/-- the first-population trial of the K160 witness is `Cert.Pc`/`Cert.P`; second population: -/
def secondU : ℕ → ℝ := trialSeqS Cert.Pc Cert.P
def secondV : ℕ → ℝ := trialSeqS Cert.Vc Cert.V

theorem second_hu : Summable (fun k => |secondU k|) := (trialSeqS_summable Cert.tailsP).1
theorem second_hv : Summable (fun k => |secondV k|) := (trialSeqS_summable Cert.tailsV).1

theorem second_field_sum : ((Cert.MX : ℚ) : ℝ) + ((Cert.MY : ℚ) : ℝ) = K160.fieldCap := by
  norm_num [Cert.MX, Cert.MY, K160.fieldCap]

theorem second_norm_le :
    2 * barrierTrialNormSq secondU + barrierTrialNormSq secondV / 2 ≤ K160.normCap := by
  have h := Cert.weighted_norm_le
  have h2 : (((2 * Cert.NP + Cert.NV / 2 : ℚ)) : ℝ) = K160.normCap := by
    norm_num [Cert.NP, Cert.NV, K160.normCap]
  unfold secondU secondV
  linarith

theorem second_row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
    rowFieldG (11 / 29) (3 / 29) (39 / 29) secondU secondV x ≤ ((Cert.MX : ℚ) : ℝ) := by
  intro x hx
  have h := Cert.row_sup_S x hx
  have e : rowFieldS Cert.R Cert.Pc Cert.Vc Cert.P Cert.V = rowFieldG (11 / 29) (3 / 29) (39 / 29) secondU secondV := by
    unfold rowFieldS secondU secondV
    norm_num [Cert.R]
  rw [e] at h
  exact h

theorem second_column_sup : ∀ s ∈ Ioo (0 : ℝ) 1,
    colFieldG (9 / 58) (3 / 58) secondV s ≤ ((Cert.MY : ℚ) : ℝ) := by
  intro s hs
  have h := Cert.column_sup_S s hs
  have e : colFieldS Cert.C Cert.Vc Cert.V = colFieldG (9 / 58) (3 / 58) secondV := by
    unfold colFieldS secondV
    norm_num [Cert.C]
  rw [e] at h
  exact h

theorem second_residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, (401 / 2500 : ℝ) ≤ |x| →
    Analytic.resFieldGen (53 / 58) secondU x ≤ K160.residualCap := by
  intro x hx hg
  have h := Cert.residual_sup_S x hx hg
  have e : Analytic.resFieldGen (53 / 58) secondU x = resFieldW (((53 / 58 : ℚ)) : ℝ) (trialSeqS Cert.Pc Cert.P) x := by
    unfold Analytic.resFieldGen resFieldW secondU
    norm_num
  rw [e]
  have e2 : ((Cert.MR : ℚ) : ℝ) = K160.residualCap := by norm_num [Cert.MR, K160.residualCap]
  linarith

theorem second_near_sup_d58 : ∀ y ∈ Ioo (0 : ℝ) 1,
    -(53 / 58 : ℝ) * Real.log (1 + y ^ 2) + (47 / 58 : ℝ) * Real.log y - secondU 1 * y ≤ -(77 / 100 : ℝ) :=
  fun y hy => Cert.near_residual_field_le_d58 Cert.first_lower hy.1 hy.2.le

/-- Bank K160 with the second-population hypotheses of `measure_592_of_certificates` discharged
(gap `g = 401/2500`).  Remaining: the circle certificate, the first-population trial `F`, and `near_sup`
at the budget cap `nearCap` (see the module docstring: the cap `-39/50` is not valid for the weight `47/58`). -/
theorem measure_592_second_population
    {rc C wc : ℝ} (hr1 : 1 < rc) (hr2 : rc ≤ 2)
    (hcirc : Analytic.GapCircleBound Odd.design (2 * (401 / 2500 : ℝ) / (1 + (401 / 2500 : ℝ) ^ 2)) rc C wc)
    (hwc : wc < K160.rho - 58 * K160.secondCost)
    (F : Analytic.FirstTrialBounds Odd.design K160.target K160.firstCost)
    (near_sup : ∀ y ∈ Ioo (0 : ℝ) 1,
      -Analytic.gRes Odd.design * Real.log (1 + y ^ 2) +
        (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) * Real.log y -
          secondU 1 * y ≤ nearCap) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(592 : ℝ)) < |catalan - (a : ℝ) / b| :=
  measure_592_of_certificates (g := 401 / 2500) (by norm_num) (by norm_num) (by norm_num) hr1 hr2
    hcirc hwc F secondU secondV second_hu second_hv (Cert.MX : ℚ) (Cert.MY : ℚ) second_field_sum
    second_norm_le near_sup second_row_sup second_column_sup second_residual_sup


end
end D58
end CatalanMeasure.GenD
#print axioms CatalanMeasure.GenD.D58.measure_592_second_population

#print axioms CatalanMeasure.GenD.D58.second_hu
#print axioms CatalanMeasure.GenD.D58.second_hv
#print axioms CatalanMeasure.GenD.D58.second_field_sum
#print axioms CatalanMeasure.GenD.D58.second_norm_le
#print axioms CatalanMeasure.GenD.D58.second_row_sup
#print axioms CatalanMeasure.GenD.D58.second_column_sup
#print axioms CatalanMeasure.GenD.D58.second_residual_sup
#print axioms CatalanMeasure.GenD.D58.second_near_sup_d58
