import CatalanCore.Uniform.Bank.Sevenths.PrimeBound
import CatalanCore.Uniform.Bank.Sevenths.Tropical
import CatalanCore.Uniform.Content.BankShared.FixedBudget
import CatalanCore.Uniform.Content.BankShared.BudgetAdd
import CatalanCore.Uniform.Content.BankShared.CrudeLog
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open Finset CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.SmallPrimes

noncomputable def rankExceptions : Finset ℕ := Icc 2 rankPrimeCutoff

theorem rankExceptions_prime (p : ℕ) (hp : p ∈ rankExceptions) : 2 ≤ p :=
  (Finset.mem_Icc.1 hp).1

noncomputable def seventhsBudget (a : Fin 6) : SmallBudget :=
  (SmallBudget.fixedCrude rankExceptions rankExceptions_prime (cFr (seventhsFrameAt a))).add
    ((SmallBudget.sqrtLog 14 (2 * (cFr (seventhsFrameAt a) + 12))).add SmallBudget.unit)

theorem seventhsPrice_prefix (a : Fin 6) (depth : ℕ)
    (i : (F7.family (seventhsFrameAt a) depth).ι) (hr : i.1 % 2 = 0)
    (p : ℕ) [hp : Fact p.Prime] (hpr : p ≤ i.1) :
    (seventhsPrice a depth i p : ℝ) ≤ (13 / 6 : ℝ) * i.1 + (seventhsBudget a).X i.1 p := by
  let c := cFr (seventhsFrameAt a)
  let BF := SmallBudget.fixedCrude rankExceptions rankExceptions_prime c
  let BS := SmallBudget.sqrtLog 14 (2 * (c + 12))
  have hf := BF.nonneg i.1 p
  have hs := BS.nonneg i.1 p
  have hu := SmallBudget.unit.nonneg i.1 p
  have hc := seventhsPrice_crude a depth i hr p
  have hcQ : (seventhsPrice a depth i p : ℝ) ≤ Ecrude c i.1 p := by exact_mod_cast hc
  have hr0 : (0 : ℝ) ≤ i.1 := Nat.cast_nonneg _
  change _ ≤ (13 / 6 : ℝ) * i.1 + (BF.X i.1 p + (BS.X i.1 p + SmallBudget.unit.X i.1 p))
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
    · have hp64 : 64 ≤ p := by have := rankPrimeCutoff_ge_sixtyFour; omega
      obtain ⟨lev, ht⟩ := sevenths_tropical_price a depth i hr p hp64 (by have := hp.out.two_le; omega) (by omega)
      have hraw : tropVal (HW lev p i.1 (F7.borderSize i.1)) ≤ 2 * (i.1 + F7.borderSize i.1) := by
        apply tropVal_le_of_forall
        intro σ
        calc ∑ b, HW lev p i.1 (F7.borderSize i.1) (σ b) b ≤ ∑ _b : Fin i.1 ⊕ Fin (F7.borderSize i.1), 2 :=
              Finset.sum_le_sum (fun b _ => wt_le_two _ _ _ _)
             _ = _ := by simp [mul_comm]
      have hP : (seventhsPrice a depth i p : ℝ) ≤ 2 * ((i.1 : ℝ) + F7.borderSize i.1) := by
        exact_mod_cast ht.trans hraw
      have hm : (12 : ℝ) * F7.borderSize i.1 ≤ i.1 + 6 := by exact_mod_cast (F7_border_round hr).1
      have he : SmallBudget.unit.X i.1 p = 1 := by simp [SmallBudget.unit, SmallBudget.ofCutoff, hpr]
      rw [he]
      linarith

#print axioms seventhsPrice_prefix
end CatalanCore.Uniform.Bank.Sevenths
