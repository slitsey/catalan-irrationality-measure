import Mathlib.Tactic
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
/-- Fixed bound for all certificate denominators and rational load/witness units. -/
def rankPrimeCutoff : ℕ := 757642551055354749996506551595817222881370572249524910
theorem rankPrimeCutoff_ge_sixtyFour : 64 ≤ rankPrimeCutoff := by decide +kernel
end CatalanCore.Uniform.Bank.Sevenths
