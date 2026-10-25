module
public import CatalanLambda.Cert.LogBounds
public import Lean.Elab.Tactic.Cbv
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.FastArithmetic
/-- Use primitive big-integer division instead of one recursive step per shifted bit. -/
@[cbv_eval] theorem shiftRight_fast (n k : ℕ) : Nat.shiftRight n k = n / 2^k :=
  Nat.shiftRight_eq_div_pow n k
/-- Use primitive multiplication instead of recursively doubling for every bit. -/
@[cbv_eval] theorem shiftLeft_fast (n k : ℕ) : Nat.shiftLeft n k = n * 2^k :=
  Nat.shiftLeft_eq n k
end CatalanCore.Cert.QuarterContour.FastArithmetic
#print axioms CatalanCore.Cert.QuarterContour.FastArithmetic.shiftRight_fast