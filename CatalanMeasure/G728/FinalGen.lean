module
public import CatalanMeasure.G728.Main
public import CatalanMeasure.G728.Glue
public import CatalanMeasure.G728.Norm
public import CatalanMeasure.Parametric.GapMain
public import CatalanMeasure.Parametric.U6Main
@[expose] public section
/-! Final assembly, generic in the three field sup facts (so it can be checked before the certificates). -/
namespace CatalanMeasure.G728
open CatalanMeasure.Parametric CatalanMeasure.Cert OAI.InternalCatalan Filter Set

def firstTrial728' : FirstTrialBoundsAt target728 strongFirstCost :=
  retarget728 gapFirstTrial (by rfl) (by rfl) (by rfl)

def secondTrial728
    (row : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, rowFieldS R Pc Vc P V x ≤ (MX : ℝ))
    (col : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldS C Vc V s ≤ (MY : ℝ))
    (res : ∀ x ∈ Icc (-1 : ℝ) 1, (401 / 2500 : ℝ) ≤ |x| → resFieldS Pc P x ≤ (MR : ℝ)) :
    SecondTrialBoundsOn target728 residual728 (-(3/4:ℝ)) secondCost728 gapAtomDomain :=
  secondTrialOfFieldsS (target := target728) (residual := residual728) (cost := secondCost728)
    (normCap := normCap728) (fieldCap := fieldCap728) (G := gapAtomDomain)
    Pc Vc P V tailsP tailsV R rfl C rfl (MX : ℝ) (MY : ℝ) first_lower
    (by have h := weighted_norm_le
        refine h.trans (le_of_eq ?_)
        norm_num [normCap, normCap728])
    (by norm_num [MX, MY, fieldCap728])
    row col
    (fun x hx hg => by
      have hg' : (401 / 2500 : ℝ) ≤ |x| := by
        simpa [gapAtomDomain, physicalAtomGap] using hg
      have := res x hx hg'
      refine this.trans (le_of_eq ?_)
      norm_num [MR, residual728])
    (fun {a t} ha ht => second_budget728 ha ht)

theorem measure_728_of_sups
    (row : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, rowFieldS R Pc Vc P V x ≤ (MX : ℝ))
    (col : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldS C Vc V s ≤ (MY : ℝ))
    (res : ∀ x ∈ Icc (-1 : ℝ) 1, (401 / 2500 : ℝ) ≤ |x| → resFieldS Pc P x ≤ (MR : ℝ)) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(728 : ℝ)) < |catalan - (a : ℝ) / b| :=
  measure_728_of_bounds u6_combined_content firstTrial728' (secondTrial728 row col res)

theorem measure_2183_of_sups
    (row : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, rowFieldS R Pc Vc P V x ≤ (MX : ℝ))
    (col : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldS C Vc V s ≤ (MY : ℝ))
    (res : ∀ x ∈ Icc (-1 : ℝ) 1, (401 / 2500 : ℝ) ≤ |x| → resFieldS Pc P x ≤ (MR : ℝ)) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(2183 : ℝ)) < |catalan - (a : ℝ) / b| :=
  measure_2183_of_bounds u6_combined_content firstTrial728' (secondTrial728 row col res)

end CatalanMeasure.G728
