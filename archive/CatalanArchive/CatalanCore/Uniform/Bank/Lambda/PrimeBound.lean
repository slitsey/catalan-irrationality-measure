import Mathlib.Tactic
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda

/-- Conservative fixed cutoff for every supplied rational numerator/denominator
and every basis-change denominator. It is not a variable asymptotic cutoff. -/
def rankPrimeCutoff : ℕ := 21928061945868238216641049838150781764

theorem rankPrimeCutoff_ge_twentyNine : 29 ≤ rankPrimeCutoff := by decide +kernel

#print axioms rankPrimeCutoff_ge_twentyNine
end CatalanCore.Uniform.Bank.Lambda
