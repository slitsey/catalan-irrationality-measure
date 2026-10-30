import CatalanCore.Uniform.Content.BankShared.CompactBudget
import CatalanCore.Uniform.Bank.Lambda.Price
import CatalanCore.Uniform.Bank.Lambda.PrimeBound
import CatalanCore.Uniform.Content.BankShared.FixedBudget
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Uniform CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Content.BankShared

noncomputable def compactScale (K : ℕ) : ℕ := K * rankPrimeCutoff + 14 * K * K

noncomputable def compactError (sgn : Bool) (K : ℕ) : ℝ :=
  (48 + 2 * (cFr (lambdaFrame sgn) : ℝ)) * compactScale K *
    (Real.log ((compactScale K : ℕ) + 1) + 1)

theorem compactError_nonneg (sgn : Bool) (K : ℕ) : 0 ≤ compactError sgn K := by
  have hl : 0 ≤ Real.log ((compactScale K : ℕ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (compactScale K); linarith)
  unfold compactError
  positivity

/-- No compact-window cover needs to omit a small or higher-level prime. -/
theorem lambdaPrice_compact_bad (sgn : Bool) (depth K : ℕ)
    (i : (FL.family (lambdaFrame sgn) depth).ι) (hr : i.1 % 2 = 0)
    (p : ℕ) [hp : Fact p.Prime] (hband : i.1 ≤ K * p)
    (hbad : p ≤ rankPrimeCutoff ∨ p * p ≤ 14 * i.1) :
    (lambdaPrice sgn depth i p : ℝ) ≤ compactError sgn K := by
  have hscale : i.1 ≤ compactScale K := compact_bad_scale K rankPrimeCutoff 14 i.1 p hp.out.pos hband hbad
  have hprice := lambdaPrice_crude sgn depth i hr p
  have hP : (lambdaPrice sgn depth i p : ℝ) ≤ Ecrude (cFr (lambdaFrame sgn)) i.1 p := by exact_mod_cast hprice
  exact hP.trans (Ecrude_le_of_scale_le (cFr (lambdaFrame sgn)) (compactScale K) i.1 p hp.out.two_le hscale)

#print axioms lambdaPrice_compact_bad
end CatalanCore.Uniform.Bank.Lambda