module

public import CatalanCore.Uniform.Bank.Plane1.Data.BankP
public import CatalanCore.Uniform.Bank.Plane1.Data.BankM

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 1 content, closed form: `PlaneBankOKC` for both supports and the plane content (wave H5a-closed)

**`planeContent_data : PlaneContent planeLam`**: for every plane frame (all weights, both supports) the even-scale
family of `altGeom (1/6)` has the scaled content `Λ = planeLam` (ledger P109, P115). -/

namespace CatalanCore.Uniform.Bank.Plane1.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

open CatalanCore.Uniform.Bank.Plane1

theorem planeBankP_ok : PlaneBankOKC .plus bankP where
  check := bankP_check
  shifts := rfl
  alpha := by norm_num [planeC, bankP, eHeadP, planeHeadC, qq]
  cat := planeCatOf_plane kPresP
  hQ := by decide
  hP := by decide
  hM := by decide
  ht0 := by norm_num [bankP, eHeadP, planeHeadC, qq]
  hα0 := by norm_num [bankP, eHeadP, planeHeadC, qq]
  hcF := by decide
  hdepth := planeDepth_le

theorem planeBankM_ok : PlaneBankOKC .minus bankM where
  check := bankM_check
  shifts := rfl
  alpha := by norm_num [planeC, bankM, eHeadM, planeHeadC, qq]
  cat := planeCatOf_plane kPresM
  hQ := by decide
  hP := by decide
  hM := by decide
  ht0 := by norm_num [bankM, eHeadM, planeHeadC, qq]
  hα0 := by norm_num [bankM, eHeadM, planeHeadC, qq]
  hcF := by decide
  hdepth := planeDepth_le

/-- **The content `Λ = planeLam` of the plane 1 (all weights, both supports).** -/
theorem planeContent_data : PlaneContent ((planeLam : ℚ) : ℝ) :=
  planeContent_of_banksC planeBankP_ok planeBankM_ok rfl

end CatalanCore.Uniform.Bank.Plane1.Data

#print axioms CatalanCore.Uniform.Bank.Plane1.Data.planeContent_data
