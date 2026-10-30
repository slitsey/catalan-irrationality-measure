import CatalanCore.Uniform.Bank.Lambda.Price
import CatalanCore.Uniform.Bank.Lambda.Tropical
import CatalanCore.Uniform.Bank.Lambda.Rounding
import CatalanCore.Uniform.Bank.Lambda.PrimeBound
import CatalanCore.Uniform.Content.BankShared.FixedBudget
import CatalanCore.Uniform.Content.BankShared.BudgetAdd
import CatalanCore.Uniform.Content.BankShared.CrudeLog
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open Finset CatalanCore CatalanCore.Uniform CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.SmallPrimes

noncomputable def rankExceptions : Finset ℕ := Icc 2 rankPrimeCutoff

theorem rankExceptions_two (p : ℕ) (hp : p ∈ rankExceptions) : 2 ≤ p :=
  (Finset.mem_Icc.1 hp).1

noncomputable def lambdaBudget (sgn : Bool) : SmallBudget :=
  (SmallBudget.fixedCrude rankExceptions rankExceptions_two (cFr (lambdaFrame sgn))).add
    ((SmallBudget.sqrtLog 14 (2 * (cFr (lambdaFrame sgn) + 12))).add SmallBudget.unit)

/-- The finite exceptional set and higher levels cost only a small-prime budget. -/
theorem lambdaPrice_prefix (sgn : Bool) (depth : ℕ)
    (i : (FamE (lambdaFrame sgn) depth).ι) (hi : (FamE (lambdaFrame sgn) depth).Adm i)
    (p : ℕ) [hp : Fact p.Prime] (hpr : p ≤ i.1) :
    (lambdaPrice sgn depth i p : ℝ) ≤ (11 / 5 : ℝ) * i.1 + (lambdaBudget sgn).X i.1 p := by
  let c := cFr (lambdaFrame sgn)
  let BF := SmallBudget.fixedCrude rankExceptions rankExceptions_two c
  let BS := SmallBudget.sqrtLog 14 (2 * (c + 12))
  have hf := BF.nonneg i.1 p
  have hs := BS.nonneg i.1 p
  have hu := SmallBudget.unit.nonneg i.1 p
  have hc := lambdaPrice_crude sgn depth i hi.2 p
  have hcQ : (lambdaPrice sgn depth i p : ℝ) ≤ Ecrude c i.1 p := by exact_mod_cast hc
  have hr0 : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg _
  change _ ≤ (11 / 5 : ℝ) * i.1 + (BF.X i.1 p + (BS.X i.1 p + SmallBudget.unit.X i.1 p))
  by_cases hfix : p ≤ rankPrimeCutoff
  · have hm : p ∈ rankExceptions := Finset.mem_Icc.2 ⟨hp.out.two_le, hfix⟩
    have he : BF.X i.1 p = (Ecrude c i.1 p : ℝ) := by simp [BF, SmallBudget.fixedCrude, hm]
    rw [he]
    linarith
  · by_cases hsq : p * p ≤ 14 * i.1
    · have he := SmallBudget.sqrtLog_X_of 14 (2 * (c + 12)) i.1 p hsq
      have hE := Ecrude_log_bound c i.1 p hp.out.two_le
      have hEQ : (Ecrude c i.1 p : ℝ) ≤ (2 * (c + 12) : ℕ) * (i.1 : ℝ) * ((Nat.log 2 i.1 : ℝ) + 1) := by
        exact_mod_cast hE
      change BS.X i.1 p = _ at he
      rw [he]
      linarith
    · have hp5 : 5 ≤ p := by have := rankPrimeCutoff_ge_twentyNine; omega
      have hr1 : 1 ≤ i.1 := by have := hp.out.pos; omega
      have hr2 : 2 ≤ i.1 := by have := hi.2; omega
      have hm := (FL_border_round hi.2).1
      have hsimple : 4 * (i.1 + 2 * FL.borderSize i.1) < p * p := by nlinarith
      have ht := lambda_tableT_gle sgn depth i hi hr1 p hp5 hsimple
      have hpT := lambdaPrice_le sgn depth i hi.2 p _ ht
      have hraw : CatalanFrames.HybGen.XGm (lambdaHybInst sgn) i.1 (FL.borderSize i.1) p ≤
          2 * (i.1 + FL.borderSize i.1) := by
        apply tropVal_le_of_forall
        intro σ
        calc ∑ b, HW (lambdaHybInst sgn).lev p i.1 (FL.borderSize i.1) (σ b) b ≤
              ∑ _b : Fin i.1 ⊕ Fin (FL.borderSize i.1), 2 :=
                Finset.sum_le_sum (fun b _ => wt_le_two _ _ _ _)
             _ = _ := by simp [mul_comm]
      have hP : (lambdaPrice sgn depth i p : ℝ) ≤ 2 * ((i.1 : ℝ) + FL.borderSize i.1) := by
        exact_mod_cast hpT.trans hraw
      have hmQ : (10 : ℝ) * FL.borderSize i.1 ≤ i.1 + 5 := by exact_mod_cast hm
      have he : SmallBudget.unit.X i.1 p = 1 := by simp [SmallBudget.unit, SmallBudget.ofCutoff, hpr]
      rw [he]
      linarith

#print axioms lambdaPrice_prefix
end CatalanCore.Uniform.Bank.Lambda