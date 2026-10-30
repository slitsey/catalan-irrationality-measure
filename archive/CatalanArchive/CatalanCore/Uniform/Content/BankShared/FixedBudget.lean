import CatalanCore.Uniform.Content.SmallPrimes.Budget
import CatalanCore.Uniform.Content.BankShared.ExceptionSmall
set_option Elab.async false
namespace CatalanCore.Uniform.Content.BankShared
open Finset Filter CatalanCore.Uniform.Content.SmallPrimes
open scoped Classical

/-- Full crude prices on any fixed finite exceptional set form a subquadratic budget. -/
noncomputable def SmallBudget.fixedCrude (F : Finset ℕ) (hF : ∀ p ∈ F, 2 ≤ p) (c : ℕ) :
    SmallBudget where
  X := fun r p => if p ∈ F then (Ecrude c r p : ℝ) else 0
  cut := fun _ => F.sup id
  nonneg := fun r p => by split_ifs <;> positivity
  supp := fun r p hp => by
    have hn : p ∉ F := by
      intro h
      have hle : p ≤ F.sup id := Finset.le_sup (f := id) h
      omega
    simp only [if_neg hn]
  small := fun ε hε => by
    filter_upwards [fixed_exception_E_crude_small F hF c ε hε] with r hr
    let S := (range (F.sup id + 1)).filter Nat.Prime
    have he : (∑ p ∈ S, (if p ∈ F then (Ecrude c r p : ℝ) else 0) * Real.log p) =
        ∑ p ∈ S.filter (fun p => p ∈ F), (Ecrude c r p : ℝ) * Real.log p := by
      conv_rhs => rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> simp
    change (∑ p ∈ S, (if p ∈ F then (Ecrude c r p : ℝ) else 0) * Real.log p) ≤ _
    rw [he]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hr
    · intro p hp
      exact (Finset.mem_filter.1 hp).2
    · intro p _ _
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

theorem Ecrude_le_of_scale_le (c R r p : ℕ) (hp : 2 ≤ p) (hr : r ≤ R) :
    (Ecrude c r p : ℝ) ≤ (48 + 2 * (c : ℝ)) * R * (Real.log ((R : ℝ) + 1) + 1) := by
  have h := Ecrude_le c hp r
  have hR : (r : ℝ) ≤ R := by exact_mod_cast hr
  have hl : Real.log ((r : ℝ) + 1) ≤ Real.log ((R : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hl0 : 0 ≤ Real.log ((r : ℝ) + 1) + 1 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (r : ℝ) + 1 by have := Nat.cast_nonneg (α := ℝ) r; linarith)
    linarith
  calc _ ≤ (48 + 2 * (c : ℝ)) * r * (Real.log ((r : ℝ) + 1) + 1) := h
       _ ≤ (48 + 2 * (c : ℝ)) * R * (Real.log ((R : ℝ) + 1) + 1) := by
         apply mul_le_mul
         · exact mul_le_mul_of_nonneg_left hR (by positivity)
         · linarith
         · exact hl0
         · positivity

#print axioms SmallBudget.fixedCrude
#print axioms Ecrude_le_of_scale_le
end CatalanCore.Uniform.Content.BankShared
