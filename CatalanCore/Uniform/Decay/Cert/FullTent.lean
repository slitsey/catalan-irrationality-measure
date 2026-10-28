module

public import CatalanCore.Uniform.Decay.Assembly.Absorb
public import CatalanCore.Decay.Rect.IntegR

@[expose] public section

/-!
# `FullN` at the frame constant is a `Tent` matrix on the node lists (lane D, package D5)

For distinct node lists (common nodes `c`, border rows `xs`, border columns `ys`, pairwise
disjoint) the retained-pencil matrix `FullN Fr c xs ys Fr.const` equals
`Matrix.of fun p q => Fr.Tent (rowNode p) (colNode q)` on `ι ⊕ κ`.  Reindexing by an equivalence
`ι ⊕ κ ≃ Fin k` gives the `Tent` matrix to which `Frame.theoremN_rect` applies.
-/

namespace CatalanCore.Uniform.Decay.Cert

open Finset Matrix CatalanCore Rect

theorem fullN_eq_tent (Fr : Frame) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (c : ι → ℕ) (xs ys : κ → ℕ) (hc : Function.Injective c)
    (hcy : ∀ a j, c a ≠ ys j) (hxc : ∀ i b, xs i ≠ c b) (hxy : ∀ i j, xs i ≠ ys j) :
    FullN Fr c xs ys (Fr.const : ℝ) =
      Matrix.of fun p q => Fr.Tent (Sum.elim c xs p) (Sum.elim c ys q) := by
  ext p q
  rcases p with a | i <;> rcases q with b | j
  · have he : (c a = c b) ↔ a = b := ⟨fun h => hc h, fun h => by rw [h]⟩
    simp [FullN, Blk, blkA, Matrix.fromBlocks, Matrix.one_apply, Frame.Tent, he, add_comm]
  · simp [FullN, Blk, blkB, Matrix.fromBlocks, Frame.Tent, hcy a j]
  · simp [FullN, Blk, blkC, Matrix.fromBlocks, Frame.Tent, hxc i b]
  · simp [FullN, Blk, blkD, Matrix.fromBlocks, Frame.Tent, hxy i j]

end CatalanCore.Uniform.Decay.Cert
