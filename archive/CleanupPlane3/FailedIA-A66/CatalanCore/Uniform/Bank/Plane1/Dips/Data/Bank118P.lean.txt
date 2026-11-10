module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Numerics
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.F118
open CatalanCore CatalanCore.Uniform CatalanCore.Measure CatalanFrames.P6
open CatalanCore.Uniform.Bank.Plane1 CatalanCore.Uniform.Bank.Plane1.Dips
abbrev bankP := Content118.bankP
abbrev dipLamP := dip18Lam
theorem bankP_check := Content118.bankP_check
theorem bankP_ok := Content118.bankP_ok
theorem dip_1_18_plus_point :
    MeasureLBAt (chi3L2+((1/18:ℚ):ℝ)*Real.pi^2) ((DipD.ccert:ℝ)/((DipD.Dt:ℝ)-(dip18Lam:ℝ))) ∧
      Irrational (chi3L2+((1/18:ℚ):ℝ)*Real.pi^2) := by
  have h := dip_point (1/4) Content118.quarter_pos 64 Support.plus 4 (-3) (-1)
    (by norm_num) (by norm_num) bankP Content118.dipBudget 0 bankP_ok
    (quarter_decay Support.plus 4 (-3) (-1) (by norm_num) 64)
    (by exact_mod_cast dip18_eta) (by exact_mod_cast dip18_cc)
    (Content118.quarter_nv0_even Support.plus 4 (-3) (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have ht : planeT Support.plus 4 (-3)=(1/18:ℚ) := by simp only [planeT,Support.sgn];norm_num
  rw [ht] at h
  exact h
theorem dip_1_18_plus_measure :
    MeasureLBAt (chi3L2+((1/18:ℚ):ℝ)*Real.pi^2) ((4373/250:ℚ):ℝ) ∧
      Irrational (chi3L2+((1/18:ℚ):ℝ)*Real.pi^2) :=
  ⟨MeasureLBAt.mono (by exact_mod_cast (le_of_lt dip18_mu)) dip_1_18_plus_point.1,dip_1_18_plus_point.2⟩
end CatalanCore.Uniform.Bank.Plane1.Dips.Data.F118
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Data.F118.bankP_check
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Data.F118.dip_1_18_plus_point
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Data.F118.dip_1_18_plus_measure
