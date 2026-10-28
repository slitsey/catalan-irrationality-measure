module

public import CatalanCore.Uniform.Content.Hybrid.DigammaPrice
public import CatalanCore.Arith.Hybrid.PrincipalMinor
public import CatalanCore.Rect.Full

@[expose] public section

/-!
# Deletion members: tropical and rank transfers (lane H5, Theorem SD, tropical and rank layers)

The deletion member is the determinant of `Rect.FullN` on the retained common nodes `S` and the
FULL border.  Two transfers, both applied to the member's own matrix (no valuation of the full
determinant is ever inherited):

* **Tropical** (`member_gle_trop`): any entry table `W` valid for the full hybrid matrix
  prices the member at `tropVal W`, with no debit.  A permutation of the member extends to the
  full matrix by the identity on the deleted pairs, whose weights are `≥ 0`.
* **Rank** (`fullN_det_eq_loewner_det`, `member_gle_digamma`): the member matrix is the actual
  Loewner matrix `loewner a b f e` of the rational digamma frame on the member's own node maps
  `Sum.elim common xs`, `Sum.elim common ys` (index `S ⊕ κ`).  The H1 theorem
  `gle_det_digamma` therefore applies verbatim to the member, with `h = |S| + m` and the
  member's own kernel data, giving the hybrid rank price with no leading debit.
-/

open Polynomial Finset Matrix CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Rect

namespace CatalanCore.Uniform.Content.Member

section Trop

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The embedding of the member index `S ⊕ κ` into the full index `ι ⊕ κ`. -/
def memberEmbedding (S : Finset ι) : (S ⊕ κ) ↪ (ι ⊕ κ) where
  toFun := Sum.map Subtype.val id
  inj' := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b <;>
      simp only [Sum.map, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, id_eq] at h
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
    · cases h
    · cases h
    · exact congrArg Sum.inr (Sum.inr.inj h)

/-- **Tropical transfer to a deletion member (debit 0).**  An entry table valid for the full
hybrid matrix prices every principal common-node restriction. -/
theorem member_gle_trop (Fr : Frame) (common : ι → ℕ) (xs ys : κ → ℕ) (S : Finset ι)
    {p : ℕ} [Fact p.Prime] (W : ι ⊕ κ → ι ⊕ κ → ℕ)
    (hW : ∀ a b, GLE p (W a b) (FullN Fr common xs ys (X : ℚ[X]) a b)) :
    GLE p (tropVal W) (FullN Fr (fun a : S => common a.1) xs ys (X : ℚ[X])).det := by
  let e := memberEmbedding (κ := κ) S
  have h : GLE p (tropVal (fun a b : S ⊕ κ => W (e a) (e b)))
      (FullN Fr (fun a : S => common a.1) xs ys (X : ℚ[X])).det := by
    apply det_gle
    intro a b
    have he := hW (e a) (e b)
    rcases a with a | a <;> rcases b with b | b <;>
      simpa [e, memberEmbedding, FullN, Blk, blkA, blkB, blkC, blkD,
        Matrix.fromBlocks, Matrix.one_apply] using he
  exact h.mono (tropVal_embedding_le W e)

end Trop

section Digamma

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Node maps of a member: rows are the retained common nodes then the row border, columns the
retained common nodes then the column border. -/
def memberRows (common : ι → ℕ) (xs : κ → ℕ) (S : Finset ι) : S ⊕ κ → ℕ :=
  Sum.elim (fun a => common a.1) xs

def memberCols (common : ι → ℕ) (ys : κ → ℕ) (S : Finset ι) : S ⊕ κ → ℕ :=
  Sum.elim (fun a => common a.1) ys

/-- The member matrix is the actual Loewner matrix of the frame on the member's node maps,
provided the frame is presented by prefixes `f, e` and the node sets are disjoint. -/
theorem fullN_eq_loewner (Fr : Frame) (f e : ℕ → ℚ)
    (hMn : ∀ a b, Fr.Mn a b = if a = b then -e a else (f b - f a) / ((b : ℚ) - a))
    (common : ι → ℕ) (xs ys : κ → ℕ) (hc : Function.Injective common)
    (hxc : ∀ i j, xs i ≠ common j) (hyc : ∀ i j, ys i ≠ common j) (hxy : ∀ i j, xs i ≠ ys j)
    (S : Finset ι) :
    FullN Fr (fun a : S => common a.1) xs ys (X : ℚ[X]) =
      Hybrid.loewner (memberRows common xs S) (memberCols common ys S) f e := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · by_cases hab : a = b
    · subst hab
      simp [FullN, Blk, blkA, Matrix.fromBlocks, Matrix.one_apply, Hybrid.loewner,
        memberRows, memberCols, hMn, sub_eq_add_neg, add_comm]
    · have hne : common a.1 ≠ common b.1 := fun h => hab (Subtype.ext (hc h))
      simp [FullN, Blk, blkA, Matrix.fromBlocks, Matrix.one_apply, Hybrid.loewner,
        memberRows, memberCols, hab, hne, hMn]
  · have hne : common a.1 ≠ ys b := fun h => hyc b a.1 h.symm
    simp [FullN, Blk, blkB, Matrix.fromBlocks, Hybrid.loewner, memberRows, memberCols, hne, hMn]
  · have hne : xs a ≠ common b.1 := hxc a b.1
    simp [FullN, Blk, blkC, Matrix.fromBlocks, Hybrid.loewner, memberRows, memberCols, hne, hMn]
  · have hne : xs a ≠ ys b := hxy a b
    simp [FullN, Blk, blkD, Matrix.fromBlocks, Hybrid.loewner, memberRows, memberCols, hne, hMn]

/-- Reduction of a member price to a price of its Loewner determinant. -/
theorem member_gle_of_loewner (Fr : Frame) (f e : ℕ → ℚ)
    (hMn : ∀ a b, Fr.Mn a b = if a = b then -e a else (f b - f a) / ((b : ℚ) - a))
    (common : ι → ℕ) (xs ys : κ → ℕ) (hc : Function.Injective common)
    (hxc : ∀ i j, xs i ≠ common j) (hyc : ∀ i j, ys i ≠ common j) (hxy : ∀ i j, xs i ≠ ys j)
    (S : Finset ι) {p : ℕ} [Fact p.Prime] {B : ℕ}
    (h : GLE p B (Hybrid.loewner (memberRows common xs S) (memberCols common ys S) f e).det) :
    GLE p B (FullN Fr (fun a : S => common a.1) xs ys (X : ℚ[X])).det := by
  rw [fullN_eq_loewner Fr f e hMn common xs ys hc hxc hyc hxy S]
  exact h

end Digamma

end CatalanCore.Uniform.Content.Member
