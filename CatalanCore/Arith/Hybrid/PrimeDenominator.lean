module
public import CatalanCore.Arith.Hybrid.Tropical
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
@[expose] public section
open Finset Polynomial CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

noncomputable def primeDenominator (N : ℕ) (E : ℕ→ℕ) : ℕ :=
  ∏p∈(range N).filter Nat.Prime,p^E p

lemma primeDenominator_pos (N : ℕ) (E : ℕ→ℕ) : 0<primeDenominator N E := by
  exact Finset.prod_pos fun p hp=>pow_pos (mem_filter.mp hp).2.pos _

/-- Any finite set of local coefficient budgets gives one integer denominator.
The polynomial and the budgets are independent of a frame or family. -/
theorem primeDenominator_integral (N : ℕ) (E : ℕ→ℕ) (f : ℚ[X])
    (hf : ∀p [Fact p.Prime],GLE p (if p<N then E p else 0) f) (i : ℕ) :
    ∃z : ℤ,(primeDenominator N E:ℚ)*f.coeff i=z := by
  apply int_of_forall_locRing
  intro p hp
  by_cases hb : p<N
  · have hmem : p∈(range N).filter Nat.Prime:=mem_filter.mpr ⟨mem_range.mpr hb,hp.out⟩
    have hgle:=hf p i
    simp only [if_pos hb] at hgle
    have hD : (primeDenominator N E:ℚ)=(p:ℚ)^E p*
        ((∏q∈((range N).filter Nat.Prime).erase p,q^E q:ℕ):ℚ) := by
      unfold primeDenominator
      rw [←Nat.cast_pow,←Nat.cast_mul]
      exact congrArg (fun n:ℕ=>(n:ℚ)) (Finset.mul_prod_erase _ (fun q=>q^E q) hmem).symm
    rw [hD]
    have hR:=int_mem_locRing (ℓ:=p) ((∏q∈((range N).filter Nat.Prime).erase p,q^E q:ℕ):ℤ)
    convert (LocRing p).mul_mem hgle (by simpa using hR) using 1 <;> push_cast <;> ring
  · have hgle:=hf p i
    simp only [if_neg hb,pow_zero,one_mul] at hgle
    exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ:=p) (primeDenominator N E:ℤ)) hgle

theorem log_primeDenominator (N : ℕ) (E : ℕ→ℕ) :
    Real.log (primeDenominator N E)=∑p∈(range N).filter Nat.Prime,(E p:ℝ)*Real.log p := by
  unfold primeDenominator
  rw [Nat.cast_prod,Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow,Real.log_pow]
  · intro p hp
    have H:=(mem_filter.mp hp).2.pos
    positivity

theorem log_primeDenominator_sub (N : ℕ) (T δ : ℕ→ℕ)
    (hδ : ∀p,p.Prime→p<N→δ p≤T p) :
    Real.log (primeDenominator N (fun p=>T p-δ p))=
      (∑p∈(range N).filter Nat.Prime,(T p:ℝ)*Real.log p)-
      ∑p∈(range N).filter Nat.Prime,(δ p:ℝ)*Real.log p := by
  rw [log_primeDenominator,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.cast_sub (hδ p (mem_filter.mp hp).2 (mem_range.mp (mem_filter.mp hp).1))]
  ring
end CatalanCore.Arith.Hybrid
