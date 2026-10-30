import CatalanCore.Uniform.Bank.Lambda.Prefix.P0
import CatalanCore.Uniform.Bank.Lambda.Prefix.P1
import CatalanCore.Uniform.Bank.Lambda.Prefix.P2
import CatalanCore.Uniform.Bank.Lambda.Prefix.P3
import CatalanCore.Uniform.Bank.Lambda.Prefix.P4
import CatalanCore.Uniform.Bank.Lambda.Prefix.P5
import CatalanCore.Uniform.Bank.Lambda.Profile.C1
import CatalanCore.Uniform.Bank.Lambda.Profile.C3
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore.Arith.Hybrid
theorem prefix0_end (C0 s0 : ℝ) : lastEnd s0 (prefix0 C0) = (1 / 835) := by rfl
theorem prefix1_end (C0 s0 : ℝ) : lastEnd s0 (prefix1 C0) = (1 / 670) := by rfl
theorem prefix2_end (C0 s0 : ℝ) : lastEnd s0 (prefix2 C0) = (1 / 505) := by rfl
theorem prefix3_end (C0 s0 : ℝ) : lastEnd s0 (prefix3 C0) = (1 / 340) := by rfl
theorem prefix4_end (C0 s0 : ℝ) : lastEnd s0 (prefix4 C0) = (1 / 175) := by rfl
theorem prefix5_end (C0 s0 : ℝ) : lastEnd s0 (prefix5 C0) = (1 / 10) := by rfl
theorem profile1_end (C0 s0 : ℝ) : lastEnd s0 (profile1 C0) = 24 / 5 := by rfl
theorem profile3_end (C0 s0 : ℝ) : lastEnd s0 (profile3 C0) = 24 / 5 := by rfl
end CatalanCore.Uniform.Bank.Lambda
