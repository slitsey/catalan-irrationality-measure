module

public import CatalanCore.Uniform.Content.Member.Combine
public import CatalanCore.Arith.Hybrid.RankWit

@[expose] public section

/-!
# Hybrid shape of a block geometry (lane H6)

`HybShape G r`: at scale `r` the common nodes of the block geometry are `[0, r)` and the border
nodes are `r + 2i` (rows) and `r + 2i + 1` (columns), i.e. the geometry is the one of the
standard hybrid matrix `Full(X)` on `Fin r ⊕ Fin m` (`Frame.hybRow`, `Frame.hybCol`).  Under this
shape the matrix of `G.geometry r` is a relabelling of `fullEntry Fr r m`, which is what the
LP1/LP2 rank witnesses (lane H3) and M3D (lane H4) are stated for.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform

namespace CatalanCore.Uniform.Content.Wire

/-- The geometry at scale `r` is the standard hybrid one (`after r m`). -/
structure HybShape (G : BlockGeom) (r : ℕ) : Prop where
  C_eq : (G.geometry r).C = Finset.range r
  xs_eq : ∀ i, (G.geometry r).xs i = r + 2 * (i : ℕ)
  ys_eq : ∀ i, (G.geometry r).ys i = r + 2 * (i : ℕ) + 1

variable {G : BlockGeom} {r : ℕ}

/-- Relabelling of the index type of the geometry matrix onto `Fin r ⊕ Fin m`. -/
def HybShape.lab (h : HybShape G r) : (G.geometry r).C ⊕ Fin (G.geometry r).k ≃
    Fin r ⊕ Fin (G.geometry r).k :=
  Equiv.sumCongr
    { toFun := fun a => ⟨a.1, by simpa [h.C_eq] using a.2⟩
      invFun := fun i => ⟨i.1, by simp [h.C_eq]⟩
      left_inv := fun a => Subtype.ext rfl
      right_inv := fun i => Fin.ext rfl }
    (Equiv.refl _)

theorem HybShape.lab_inl (h : HybShape G r) (a : (G.geometry r).C) :
    h.lab (Sum.inl a) = Sum.inl ⟨a.1, by simpa [h.C_eq] using a.2⟩ := rfl

theorem HybShape.lab_inr (h : HybShape G r) (i : Fin (G.geometry r).k) :
    h.lab (Sum.inr i) = Sum.inr i := rfl

theorem HybShape.card_C (h : HybShape G r) : (G.geometry r).C.card = r := by
  rw [h.C_eq, Finset.card_range]

/-- The geometry matrix entries are the entries of `fullEntry` under the relabelling. -/
theorem HybShape.fullN_apply (Fr : Frame) (h : HybShape G r)
    (i j : (G.geometry r).C ⊕ Fin (G.geometry r).k) :
    FullN Fr (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs (G.geometry r).ys
      (X : ℚ[X]) i j = fullEntry Fr r (G.geometry r).k (h.lab i) (h.lab j) := by
  rcases i with a | a <;> rcases j with b | b
  · simp only [FullN, Blk, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply,
      blkA, Matrix.of_apply, Matrix.one_apply, fullEntry, h.lab_inl, Frame.hybRow, Frame.hybCol,
      Sum.elim_inl, Sum.inl.injEq, Fin.mk.injEq, Subtype.ext_iff, Polynomial.algebraMap_eq]
    split_ifs <;> simp [add_comm]
  · simp [FullN, Blk, blkB, fullEntry, h.lab_inl, h.lab_inr, Frame.hybRow, Frame.hybCol, h.ys_eq, Polynomial.algebraMap_eq]
  · simp [FullN, Blk, blkC, fullEntry, h.lab_inl, h.lab_inr, Frame.hybRow, Frame.hybCol, h.xs_eq, Polynomial.algebraMap_eq]
  · simp [FullN, Blk, blkD, fullEntry, h.lab_inr, Frame.hybRow, Frame.hybCol, h.xs_eq, h.ys_eq, Polynomial.algebraMap_eq]

end CatalanCore.Uniform.Content.Wire
