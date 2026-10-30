import CatalanCore.Uniform.Bank.Lambda.Price
import CatalanCore.Uniform.Bank.Lambda.Tropical
import CatalanCore.Uniform.Bank.Lambda.Rounding
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Uniform CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Content.BankShared

/-- The same price vanishes beyond the exact finite-template endpoint. -/
theorem lambdaPrice_tail (sgn : Bool) (depth : ℕ)
    (i : (FamE (lambdaFrame sgn) depth).ι) (hi : (FamE (lambdaFrame sgn) depth).Adm i)
    (p : ℕ) [Fact p.Prime] (hcut : 24 * i.1 < 5 * p) :
    lambdaPrice sgn depth i p = 0 := by
  by_cases hr0 : i.1 = 0
  · have h := lambdaPrice_crude sgn depth i hi.2 p
    simp only [hr0, Ecrude, zero_mul] at h
    omega
  · have hr1 : 1 ≤ i.1 := by omega
    have hr2 : 2 ≤ i.1 := by have := hi.2; omega
    have hp5 : 5 ≤ p := by omega
    have hpp : p.Prime := Fact.out
    have hodd : p % 2 = 1 := by have := hpp.eq_two_or_odd; omega
    have hm := (FL_border_round hi.2).1
    have hsq : 4 * (i.1 + 2 * FL.borderSize i.1) < p * p := by nlinarith
    have hz := lambda_tableT_tail sgn i.1 (FL.borderSize i.1) p hp5 hodd hi.2 hm hcut
    have hg := lambda_tableT_gle sgn depth i hi hr1 p hp5 hsq
    rw [hz] at hg
    have h := lambdaPrice_le sgn depth i hi.2 p 0 hg
    omega

#print axioms lambdaPrice_tail
end CatalanCore.Uniform.Bank.Lambda