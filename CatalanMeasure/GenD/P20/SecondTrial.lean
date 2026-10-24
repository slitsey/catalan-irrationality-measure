module

public import CatalanMeasure.GenD.Analytic.DeltaChain
public import CatalanMeasure.GenD.P20.Budget
public import CatalanMeasure.G728.Cert.XCover
public import CatalanMeasure.G728.Cert.YCover
public import CatalanMeasure.G728.Cert.RCover
public import CatalanMeasure.G728.Norm
public import CatalanMeasure.G728.Facts
public import CatalanMeasure.Parametric.StrongNearField

@[expose] public section

/-!
# P20: the second-population certificate `SecondFieldCert twenty` (instance file)

The existing 728 witness `u = trialSeqS Pc P`, `v = trialSeqS Vc V` (`G728.Data`) with the existing
kernel-checked covers `G728.row_sup` (X), `column_sup` (Y), `residual_sup` (R) and the norm bound
`weighted_norm_le`; the cells are untouched.  Residual gap `g = 401/2500`, near cap `-3/4`
(`near_residual_field_le_three_fourths`).
-/

namespace CatalanMeasure.GenD
namespace P20
open Set Filter CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.G728
open scoped Topology
noncomputable section

def secondU : ℕ → ℝ := trialSeqS G728.Pc G728.P
def secondV : ℕ → ℝ := trialSeqS G728.Vc G728.V

theorem second_hu : Summable (fun k => |secondU k|) := (trialSeqS_summable G728.tailsP).1
theorem second_hv : Summable (fun k => |secondV k|) := (trialSeqS_summable G728.tailsV).1

theorem second_field_sum : ((G728.MX : ℚ) : ℝ) + ((G728.MY : ℚ) : ℝ) = fieldCap := by
  norm_num [G728.MX, G728.MY, fieldCap]

theorem second_norm_le :
    2 * barrierTrialNormSq secondU + barrierTrialNormSq secondV / 2 ≤ normCap := by
  have h := G728.weighted_norm_le
  have h2 : ((G728.normCap : ℚ) : ℝ) = normCap := by norm_num [G728.normCap, normCap]
  unfold secondU secondV
  linarith

theorem second_row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
    rowFieldG (((design.b0 : ℝ) + design.q0 + 2 * design.g0) / design.n0)
      (2 * (design.h0 : ℝ) / design.n0)
      (((design.n0 : ℝ) + design.b0 + design.q0 + design.g0 + design.h0) / design.n0)
      secondU secondV x ≤ ((G728.MX : ℚ) : ℝ) := by
  intro x hx
  have h := G728.row_sup x hx
  have e : rowFieldS G728.R G728.Pc G728.Vc G728.P G728.V =
      rowFieldG (((design.b0 : ℝ) + design.q0 + 2 * design.g0) / design.n0)
        (2 * (design.h0 : ℝ) / design.n0)
        (((design.n0 : ℝ) + design.b0 + design.q0 + design.g0 + design.h0) / design.n0)
        secondU secondV := by
    unfold rowFieldS secondU secondV
    norm_num [G728.R, design, Parametric.twenty]
  rw [e] at h
  exact h

theorem second_column_sup : ∀ s ∈ Ioo (0 : ℝ) 1,
    colFieldG ((design.b0 : ℝ) / design.n0) ((design.q0 : ℝ) / design.n0) secondV s ≤
      ((G728.MY : ℚ) : ℝ) := by
  intro s hs
  have h := G728.column_sup s hs
  have e : colFieldS G728.C G728.Vc G728.V =
      colFieldG ((design.b0 : ℝ) / design.n0) ((design.q0 : ℝ) / design.n0) secondV := by
    unfold colFieldS secondV
    norm_num [G728.C, design, Parametric.twenty]
  rw [e] at h
  exact h

theorem second_residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, (401 / 2500 : ℝ) ≤ |x| →
    Analytic.resFieldGen (Analytic.gRes design) secondU x ≤ residualCap := by
  intro x hx hg
  have h := G728.residual_sup x hx hg
  have e : Analytic.resFieldGen (Analytic.gRes design) secondU x =
      resFieldS G728.Pc G728.P x := by
    unfold Analytic.resFieldGen resFieldS resFieldG secondU
    rw [gRes_p20]
    norm_num
  rw [e]
  have e2 : ((G728.MR : ℚ) : ℝ) = residualCap := by norm_num [G728.MR, residualCap]
  linarith

theorem second_near_sup : ∀ y ∈ Ioo (0 : ℝ) 1,
    -Analytic.gRes design * Real.log (1 + y ^ 2) +
      (((design.n0 : ℝ) - 2 * design.g0 - 1) / design.n0) * Real.log y -
        secondU 1 * y ≤ nearCap := by
  intro y hy
  have h := near_residual_field_le_three_fourths G728.first_lower hy.1 hy.2.le
  have hθ : (((design.n0 : ℝ) - 2 * design.g0 - 1) / design.n0) = 3 / 4 := by
    norm_num [design, Parametric.twenty]
  rw [gRes_p20, hθ]
  unfold nearCap
  have e : (-3 / 4 : ℝ) = -(3 / 4) := by norm_num
  rw [e]
  exact h

/-- The second-population certificate of the 728 witness. -/
def secondCert :
    Analytic.SecondFieldCert design target residualCap nearCap secondCost
      (fun x => (401 / 2500 : ℝ) ≤ |x|) :=
  { u := secondU, v := secondV, hu := second_hu, hv := second_hv,
    MX := ((G728.MX : ℚ) : ℝ), MY := ((G728.MY : ℚ) : ℝ), normCap := normCap,
    fieldCap := fieldCap, near_sup := second_near_sup, norm_le := second_norm_le,
    field_sum := second_field_sum, row_sup := second_row_sup, column_sup := second_column_sup,
    residual_sup := second_residual_sup,
    budget := fun ha ht => second_budget_gen ha ht }

end
end P20
end CatalanMeasure.GenD
