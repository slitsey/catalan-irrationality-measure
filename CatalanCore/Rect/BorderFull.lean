module

public import CatalanCore.Arith.Hybrid.BorderCore
public import CatalanCore.Rect.Geometry

@[expose] public section

/-!
# `det Full(afterTop r m)` as a bordered matrix (MEM2C)

`afterTop r m` is `after r m` plus one extra common node `b = r + 2m`.  Reindexing the
`FullN` matrix by `Option (Fin r ⊕ Fin m)` (`none` = the new node) exhibits `Full(afterTop)` as the
matrix of `Frame.fullPoly r m` bordered by one row and one column.

* `topMat Fr r m` : the bordered matrix over `ℚ[X]`;
* `det_topMat` : `det topMat = (afterTop r m).fullPolyG Fr`;
* `topMat_inner/row/col/corner` : its entries;
* `gle_fullTop_of_rank` : the rank principle for the bordered determinant, from the rank-principle
  data of the inner block `Frame.fullPoly r m` (the same `u, v, Bbar, k` as `gle_full_of_rank`).
-/

open Polynomial Finset Matrix CatalanCore.Arith.Hybrid CatalanCore.Basic

namespace CatalanCore.Rect

variable (Fr : Frame) (r m : ℕ)

/-- The new top node. -/
abbrev topNode : ℕ := r + 2 * m

/-- The bordered matrix: rows/columns `none` (new node `r + 2m`) and `some (inl c)`, `some (inr i)`. -/
noncomputable def topMat : Matrix (Option (Fin r ⊕ Fin m)) (Option (Fin r ⊕ Fin m)) ℚ[X] :=
  Matrix.of fun a b =>
    (match a, b with
      | none, none => (X : ℚ[X])
      | some (Sum.inl c), some (Sum.inl c') => if c = c' then (X : ℚ[X]) else 0
      | _, _ => 0) +
    C (Fr.Mn (a.elim (topNode r m) (Frame.hybRow r m)) (b.elim (topNode r m) (Frame.hybCol r m)))

theorem topMat_inner (a b : Fin r ⊕ Fin m) :
    topMat Fr r m (some a) (some b) = Arith.Hybrid.fullEntry Fr r m a b := by
  rcases a with c | i <;> rcases b with c' | j <;> simp [topMat, Arith.Hybrid.fullEntry]

theorem topMat_row (a : Fin r ⊕ Fin m) :
    topMat Fr r m (some a) none = C (Fr.Mn (Frame.hybRow r m a) (topNode r m)) := by
  rcases a with c | i <;> simp [topMat]

theorem topMat_col (b : Fin r ⊕ Fin m) :
    topMat Fr r m none (some b) = C (Fr.Mn (topNode r m) (Frame.hybCol r m b)) := by
  rcases b with c | i <;> simp [topMat]

theorem topMat_corner :
    topMat Fr r m none none = X + C (Fr.Mn (topNode r m) (topNode r m)) := by
  simp [topMat]

/-- The reindexing `Option (Fin r ⊕ Fin m) ≃ Option (Fin r) ⊕ Fin m`. -/
def topEquiv : Option (Fin r ⊕ Fin m) ≃ Option (Fin r) ⊕ Fin m where
  toFun
    | none => Sum.inl none
    | some (Sum.inl c) => Sum.inl (some c)
    | some (Sum.inr j) => Sum.inr j
  invFun
    | Sum.inl none => none
    | Sum.inl (some c) => some (Sum.inl c)
    | Sum.inr j => some (Sum.inr j)
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro ((_ | _) | _) <;> rfl

/-- The node enumeration of `afterTop`, as an equivalence with `Option (Fin r)`. -/
def topCEquiv : Option (Fin r) ≃ (afterTop r m).C where
  toFun
    | none => ⟨r + 2 * m, by simp [afterTop]⟩
    | some i => ⟨i, by simp [afterTop, i.2]⟩
  invFun a := if h : (a : ℕ) < r then some ⟨a, h⟩ else none
  left_inv := by
    rintro (_ | i)
    · simp
    · simp
  right_inv := by
    intro x
    obtain ⟨a, ha⟩ := x
    have : a = r + 2 * m ∨ a < r := by
      simp only [afterTop, mem_insert, mem_range] at ha; exact ha
    by_cases h : a < r
    · simp [h]
    · simp [h]; omega

theorem det_topMat : (topMat Fr r m).det = (afterTop r m).fullPolyG Fr := by
  unfold Geometry.fullPolyG Geometry.Full
  have hk : (afterTop r m).k = m := after_k r m
  have h1 := det_fullN_reindex Fr (fun a : (afterTop r m).C => (a : ℕ)) (afterTop r m).xs
    (afterTop r m).ys (fun o : Option (Fin r) => o.elim (r + 2 * m) (fun i : Fin r => (i : ℕ)))
    (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1)
    (topCEquiv r m) (finCongr hk).symm
    (by rintro (_ | i) <;> simp [topCEquiv])
    (fun i => by rw [afterTop_xs]; simp) (fun i => by rw [afterTop_ys]; simp) (X : ℚ[X])
  rw [← h1, ← Matrix.det_submatrix_equiv_self (topEquiv r m).symm]
  congr 1
  refine Matrix.ext fun a b => ?_
  rcases a with (_ | a) | a <;> rcases b with (_ | b) | b <;>
    simp [topMat, topEquiv, FullN, Blk, blkA, blkB, blkC, blkD, Matrix.fromBlocks,
      Matrix.one_apply, Frame.hybRow, Frame.hybCol, topNode, add_comm]

/-- **Rank principle for the bordered determinant `det Full(afterTop r m)`.**  The data
`(u, v, Bbar, k)` are those of `gle_full_of_rank` for the inner block `Frame.fullPoly r m`; the new
row and column entries are `p^w`-integral. -/
theorem gle_fullTop_of_rank (p : ℕ) [Fact p.Prime] (u v : Fin r ⊕ Fin m → ℕ)
    (Bbar : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) (RatFunc (ZMod p)))
    (hB : ∀ a b, ∃ g : (LocRing p)[X],
      toQ p g = C ((p : ℚ) ^ (u a + v b)) * fullEntry Fr r m a b ∧ phiP p g = Bbar a b)
    (k : ℕ) (hrk : Bbar.rank + k ≤ r + m) (w : ℕ)
    (hr : ∀ a, (p : ℚ) ^ w * Fr.Mn (Frame.hybRow r m a) (topNode r m) ∈ LocRing p)
    (hc : ∀ b, (p : ℚ) ^ w * Fr.Mn (topNode r m) (Frame.hybCol r m b) ∈ LocRing p)
    (hd : (p : ℚ) ^ (w + w) * Fr.Mn (topNode r m) (topNode r m) ∈ LocRing p) :
    GLE p (∑ a, u a + ∑ b, v b + (w + w) - (k - 1)) ((afterTop r m).fullPolyG Fr) := by
  classical
  choose g hg1 hg2 using hB
  have hmap : (Matrix.of g).map (phiP p) = Bbar := by ext a b; simp [hg2]
  rw [← det_topMat]
  refine gle_det_border_of_rank p (topMat Fr r m) (Matrix.of g) u v
    (fun a b => by rw [topMat_inner]; exact hg1 a b) k ?_ w ?_ ?_ ?_
  · rw [hmap]; simpa using hrk
  · intro a; rw [topMat_row]; exact GLE.C_iff.2 (hr a)
  · intro b; rw [topMat_col]; exact GLE.C_iff.2 (hc b)
  · rw [topMat_corner]
    exact (GLE.X.mono (Nat.zero_le _)).add (GLE.C_iff.2 hd)

end CatalanCore.Rect
