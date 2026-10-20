module

public import CatalanCore.Arith.Hybrid.Tropical

@[expose] public section

/-! # Assignment covers from one zero rectangle

This is a weak-duality bound, with no claim of optimality.  Exceptional
weight-two edges meeting the rectangle are charged to their incident vertices.
The zero/one case follows by taking every exceptional-vertex flag to be false.
-/

open Finset

namespace CatalanCore.Arith.Hybrid

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tropVal_le_nat_dual (W : ι → ι → ℕ) (u v : ι → ℕ)
    (h : ∀ a b, W a b ≤ u a + v b) : tropVal W ≤ ∑ a, u a + ∑ b, v b := by
  obtain ⟨σ, hσ⟩ := exists_tropVal W
  rw [hσ]
  calc ∑ b, W (σ b) b ≤ ∑ b, (u (σ b) + v b) := sum_le_sum fun b _ => h (σ b) b
    _ = ∑ a, u a + ∑ b, v b := by
      rw [sum_add_distrib, Equiv.sum_comp σ]

/-- A vertex costs one unless it lies in the zero rectangle and has no
exceptional weight-two incidence. -/
def rectangleCost (inside exceptional : Prop) [Decidable inside] [Decidable exceptional] : ℕ :=
  if inside ∧ ¬ exceptional then 0 else 1

theorem zero_rectangle_cover (W : ι → ι → ℕ) (S T E F : ι → Prop)
    [DecidablePred S] [DecidablePred T] [DecidablePred E] [DecidablePred F]
    (h2 : ∀ a b, W a b ≤ 2)
    (h0 : ∀ a b, S a → T b → W a b = 0)
    (hE : ∀ a b, S a → ¬ E a → W a b ≤ 1)
    (hF : ∀ a b, T b → ¬ F b → W a b ≤ 1) :
    tropVal W ≤ ∑ a, rectangleCost (S a) (E a) +
      ∑ b, rectangleCost (T b) (F b) := by
  apply tropVal_le_nat_dual
  intro a b
  have hW := h2 a b
  by_cases ha : S a ∧ ¬ E a <;> by_cases hb : T b ∧ ¬ F b
  · simp only [rectangleCost, if_pos ha, if_pos hb, zero_add]
    exact (h0 a b ha.1 hb.1).le
  · simp only [rectangleCost, if_pos ha, if_neg hb, zero_add]
    exact hE a b ha.1 ha.2
  · simp only [rectangleCost, if_neg ha, if_pos hb, add_zero]
    exact hF a b hb.1 hb.2
  · simpa only [rectangleCost, if_neg ha, if_neg hb] using hW

theorem zero_one_rectangle_cover (W : ι → ι → ℕ) (S T : ι → Prop)
    [DecidablePred S] [DecidablePred T]
    (h1 : ∀ a b, W a b ≤ 1)
    (h0 : ∀ a b, S a → T b → W a b = 0) :
    tropVal W ≤ ∑ a, (if S a then 0 else 1) + ∑ b, (if T b then 0 else 1) := by
  have h := zero_rectangle_cover W S T (fun _ => False) (fun _ => False)
    (fun a b => (h1 a b).trans (by omega)) h0
    (fun a b _ _ => h1 a b) (fun a b _ _ => h1 a b)
  simpa only [rectangleCost, not_false_eq_true, and_true] using h

end CatalanCore.Arith.Hybrid
