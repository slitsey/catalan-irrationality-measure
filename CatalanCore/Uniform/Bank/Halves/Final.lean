import CatalanCore.Uniform.Bank.Halves.NV
import CatalanCore.Uniform.Content.Shape.Reindex
import CatalanCore.Measure.Scaling
set_option Elab.async false

namespace CatalanCore.Uniform.Bank.Halves
/-- The exact directed receipt decay rate. -/
def DH : ℚ := 3978571368316643039103 / 1000000000000000000000
/-- The exact directed receipt growth constant. -/
def cH : ℚ := 16087718322567253 / 2500000000000000
/-- The rounded-up target exponent. -/
def BH : ℚ := 327 / 50
end CatalanCore.Uniform.Bank.Halves
