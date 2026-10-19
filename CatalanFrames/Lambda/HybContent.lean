module

public import CatalanFrames.Lambda.HybPieces
public import CatalanCore.Arith.Hybrid.Extra

@[expose] public section

/-!
# λ: the hybrid content theorem (simplified route)

`lam_content_trop` : for every `ε > 0`, eventually in `r`,
`log (Dhyb lamInst r ⌊r/8⌋) ≤ (1579/420 + ε) r²`, where `1579/420 = 3.7595238 = 313/105 +
(554/105)/8 + (160/21)/64` is the tropical constant `Λ_trop(1/8)` with the trivial dual D1 on
`(0, 1/4]` (the exact `Λ_trop` = 3.7499347 replaces the `(160/21) α²` by `(118/21 + 2 log 2) α²`).
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

/-! ### The piece tables -/

noncomputable def l3 : List Piece :=
  [mkPiece 1 4 9 10 17 0 64 8, mkPiece 9 10 1 1 13 (-5) 32 4, mkPiece 1 1 5 4 7 (-3) 32 2,
   mkPiece 5 4 4 1 9 (-2) 32 4, mkPiece 4 1 5 1 5 (-1) 32 4]

noncomputable def l1 : List Piece :=
  [mkPiece 1 4 9 14 17 0 64 8, mkPiece 9 14 5 7 13 (-7) 32 4, mkPiece 5 7 1 1 9 (-7) 16 2,
   mkPiece 1 1 5 4 7 (-5) 16 2, mkPiece 5 4 4 3 9 (-6) 32 4, mkPiece 4 3 5 3 5 (-3) 32 4]

lemma l3_chain : Chain (1 / 4) l3 := by
  simp only [l3, Chain, mkPiece]
  norm_num

lemma l1_chain : Chain (1 / 4) l1 := by
  simp only [l1, Chain, mkPiece]
  norm_num

lemma l3_end : lastEnd (1 / 4) l3 = ((5 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by
  simp [l3, lastEnd, mkPiece]

lemma l1_end : lastEnd (1 / 4) l1 = ((5 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) := by
  simp [l1, lastEnd, mkPiece]

/-- The constant of the simplified route. -/
theorem lam_const :
    ((9 / 4 : ℝ) * (1 / 4) + listInt l3) / 2 + ((9 / 4 : ℝ) * (1 / 4) + listInt l1) / 2 =
      1579 / 420 := by
  simp only [l3, l1, listInt, Piece.int, mkPiece]
  norm_num

lemma l3_covers (r : ℕ) : ∀ P ∈ l3, Covers (3 : ZMod 4) (lamW r) r P := by
  intro P hP
  simp only [l3, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl
  exacts [c3_1 r, c3_2 r, c3_3 r, c3_4 r, c3_5 r]

lemma l1_covers (r : ℕ) : ∀ P ∈ l1, Covers (1 : ZMod 4) (lamW r) r P := by
  intro P hP
  simp only [l1, List.mem_cons, List.mem_nil_iff, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [c1_1 r, c1_2 r, c1_3 r, c1_4 r, c1_5 r, c1_6 r]

lemma lamW_nonneg (r p : ℕ) : 0 ≤ lamW r p := Nat.cast_nonneg _

/-! ### Class totals -/

lemma tot4 : ((Nat.totient 4 : ℕ) : ℝ) = 2 := by
  rw [show Nat.totient 4 = 2 by decide]; norm_num

lemma isUnit4_3 : IsUnit (3 : ZMod 4) := by decide
lemma isUnit4_1 : IsUnit (1 : ZMod 4) := isUnit_one

theorem class3_total {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (3 : ZMod 4) (lamW r) 0 (5 * r) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 4) + listInt l3) / 2 + ε) := by
  have h := class_total (M := 4) isUnit4_3 (α0 := 9 / 4) (t1 := 1 / 4) (by norm_num) (by norm_num)
    l3 l3_chain hε
  filter_upwards [h] with r hr
  have := hr (lamW r) (fun p _ _ _ => lam_prefix r p) (l3_covers r)
  rw [l3_end, floor_frac] at this
  simpa [tot4] using this

theorem class1_total {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (1 : ZMod 4) (lamW r) 0 (5 * r / 3) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 4) + listInt l1) / 2 + ε) := by
  have h := class_total (M := 4) isUnit4_1 (α0 := 9 / 4) (t1 := 1 / 4) (by norm_num) (by norm_num)
    l1 l1_chain hε
  filter_upwards [h] with r hr
  have := hr (lamW r) (fun p _ _ _ => lam_prefix r p) (l1_covers r)
  rw [l1_end, floor_frac] at this
  simpa [tot4] using this

end CatalanFrames.Lambda
