module

public import CatalanFrames.Lambda.HybContentT2

@[expose] public section

/-!
# λ: the content bound for `DhybT`, part 3: the exact-D1 prefix pieces and class totals for `lamWT`
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

lemma ld1_t_le : ∀ P ∈ ld1, P.t ≤ 1 / 4 := by
  intro P hP
  simp only [ld1, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> (simp only [mkPiece]; norm_num)

lemma ld1_covers_T (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) {r : ℕ} (hr : 16 ≤ r) :
    ∀ P ∈ ld1, Covers c (lamWT r) r P := by
  intro P hP
  have hw := ld1_covers c hc2 r P hP
  intro p hlo hhi hp hc
  refine max_le (hw p hlo hhi hp hc) ?_
  have ht := ld1_t_le P hP
  have h1 : (p : ℝ) ≤ P.t * r := by
    have h2 : (p : ℝ) ≤ (⌊P.t * r⌋₊ : ℝ) := by exact_mod_cast hhi
    refine h2.trans (Nat.floor_le ?_)
    have : 0 ≤ P.t := by
      by_contra hneg
      push_neg at hneg
      have : ⌊P.t * r⌋₊ = 0 := Nat.floor_of_nonpos (by nlinarith [(Nat.cast_nonneg r : (0:ℝ) ≤ r)])
      omega
    positivity
  have h4 : 4 * p ≤ r := by
    have : (p : ℝ) ≤ r / 4 := by nlinarith [(Nat.cast_nonneg r : (0:ℝ) ≤ r)]
    have : (4 * p : ℝ) ≤ r := by linarith
    exact_mod_cast this
  have h0 : eN r p = 0 := by
    rcases eN_arith r p hr hp with h | h | h | h <;> first | exact h | omega
  rw [h0]
  have := hw p hlo hhi hp hc
  have h5 := lamW_nonneg r p
  simp only [Nat.cast_zero]
  linarith

end CatalanFrames.Lambda
