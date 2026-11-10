module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Numerics
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.F118
open CatalanCore CatalanCore.Uniform CatalanCore.Measure CatalanFrames.P6
open CatalanCore.Uniform.Bank.Plane1 CatalanCore.Uniform.Bank.Plane1.Dips
abbrev bankM := Content118.bankM
abbrev dipLamM := dip18Lam
theorem bankM_check : CatalanCore.Uniform.Content.BankShared.KTerm.kcheckC bankM = true := Content118.bankM_check
theorem bankM_ok : DipBankOK (1/4) Content118.quarter_pos 64 Support.minus 4 (-3) (-1) (by norm_num) bankM Content118.dipBudget 0 := Content118.bankM_ok
theorem dip_1_18_minus_point :
    MeasureLBAt (chi3L2+((-1/18:ℚ):ℝ)*Real.pi^2) ((DipD.ccert:ℝ)/((DipD.Dt:ℝ)-(dip18Lam:ℝ))) ∧
      Irrational (chi3L2+((-1/18:ℚ):ℝ)*Real.pi^2) := by
  have h := dip_point (1/4) Content118.quarter_pos 64 Support.minus 4 (-3) (-1)
    (by norm_num) (by norm_num) bankM Content118.dipBudget 0 bankM_ok
    (quarter_decay Support.minus 4 (-3) (-1) (by norm_num) 64)
    (by exact_mod_cast dip18_eta) (by exact_mod_cast dip18_cc)
    (Content118.quarter_nv0_even Support.minus 4 (-3) (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have ht : planeT Support.minus 4 (-3)=(-1/18:ℚ) := by simp only [planeT,Support.sgn];norm_num
  rw [ht] at h
  exact h
theorem dip_1_18_minus_measure :
    MeasureLBAt (chi3L2+((-1/18:ℚ):ℝ)*Real.pi^2) ((4373/250:ℚ):ℝ) ∧
      Irrational (chi3L2+((-1/18:ℚ):ℝ)*Real.pi^2) :=
  ⟨MeasureLBAt.mono (by exact_mod_cast (le_of_lt dip18_mu)) dip_1_18_minus_point.1,dip_1_18_minus_point.2⟩
end CatalanCore.Uniform.Bank.Plane1.Dips.Data.F118
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Data.F118.bankM_check
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Data.F118.dip_1_18_minus_point
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Data.F118.dip_1_18_minus_measure
