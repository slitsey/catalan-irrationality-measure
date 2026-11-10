module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Cover
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Auto
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Plane1.Dips
def dip18Lam : ℚ := Data.Content118.bankP.Λ
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; one scalar rational comparison, complete fullZ/PRE mass retained.
theorem dip18_eta : dip18Lam<DipD.Dt := by decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; one scalar comparison.
theorem dip18_cc : (0:ℚ)<DipD.ccert := by decide +kernel
-- kcost: 1.0 s C estimate from the retained dip scalar class measured1.0s; exact fixed scalar rational division/comparison, no catalogue orprofile rechecks.
theorem dip18_mu : DipD.ccert/(DipD.Dt-dip18Lam)<(4373/250:ℚ) := by decide +kernel
end CatalanCore.Uniform.Bank.Plane1.Dips
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.dip18_eta
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.dip18_mu
