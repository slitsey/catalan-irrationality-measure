module

public import CatalanCore.Uniform.Content.Member.Combine

@[expose] public section

/-!
# Entry tables for the tropical layer from rational valuations (lane H5)

`fullN_entry_gle`: if the rational frame entry `Mn A B` at the nodes of `(a, b)` is
`p^(W a b)`-integral then the polynomial entry of `FullN` (frame entry plus `X` on the common
diagonal) satisfies `GLE p (W a b)`: the variable `X` has weight `0 ≤ W`.  So the tropical layer
`DebitLayer.tropRat` needs only the rational entry valuations (the level majorants of the bank).
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform

namespace CatalanCore.Uniform.Content.Member

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem fullN_entry_gle (Fr : Frame) (common : ι → ℕ) (xs ys : κ → ℕ) {p : ℕ} [Fact p.Prime]
    (W : ι ⊕ κ → ι ⊕ κ → ℕ)
    (hrat : ∀ a b, (p : ℚ) ^ W a b *
      Fr.Mn (Sum.elim common xs a) (Sum.elim common ys b) ∈ LocRing p) :
    ∀ a b, GLE p (W a b) (FullN Fr common xs ys (X : ℚ[X]) a b) := by
  intro a b
  have hC : GLE p (W a b) (C (Fr.Mn (Sum.elim common xs a) (Sum.elim common ys b))) :=
    GLE.C_iff.2 (hrat a b)
  have hX : ∀ i j : ι, GLE p (W (Sum.inl i) (Sum.inl j))
      (if i = j then (X : ℚ[X]) else 0) := by
    intro i j
    split_ifs
    · exact (GLE.X (p := p)).mono (Nat.zero_le _)
    · exact GLE.zero _
  rcases a with a | a <;> rcases b with b | b
  · have := (hC.add (hX a b))
    simpa [FullN, Blk, blkA, Matrix.fromBlocks, Matrix.one_apply, Matrix.add_apply] using this
  · simpa [FullN, Blk, blkB, Matrix.fromBlocks] using hC
  · simpa [FullN, Blk, blkC, Matrix.fromBlocks] using hC
  · simpa [FullN, Blk, blkD, Matrix.fromBlocks] using hC

namespace DebitLayer

variable {G : BlockGeom} {Fr : Frame} {depth : ℕ}

/-- **Tropical layer from rational entry valuations (debit 0).** -/
noncomputable def tropRat (valid : ℕ → ℕ → Prop)
    (W : ∀ r p : ℕ, (G.geometry r).C ⊕ Fin (G.geometry r).k →
      (G.geometry r).C ⊕ Fin (G.geometry r).k → ℕ)
    (hrat : ∀ r p, valid r p → ∀ [Fact p.Prime], ∀ a b, (p : ℚ) ^ W r p a b *
      Fr.Mn (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs a)
        (Sum.elim (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).ys b) ∈ LocRing p) :
    DebitLayer G Fr depth :=
  trop valid W (fun r p hv _ => fullN_entry_gle Fr (fun a : (G.geometry r).C => (a : ℕ))
    (G.geometry r).xs (G.geometry r).ys (W r p) (hrat r p hv))

end DebitLayer

end CatalanCore.Uniform.Content.Member
