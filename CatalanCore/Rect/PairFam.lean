module

public import CatalanCore.Rect.Family

@[expose] public section

/-!
# The two-member hybrid family (LAMASM)

`hybPairFam Fr d`: the members are the two NV geometries of DO, for `r` a multiple of `d` and
`m = r / d`:

* `(r, false)` : `after r m`,     degree `r`     (`Q = Frame.fullPoly r m`);
* `(r, true)`  : `afterTop r m`,  degree `r + 1`  (the same block plus a common node `r + 2m`).

`Q = det Full(X)` of the geometry (no denominator clearing).  Facts proved here:

* `natDegree_fullN_le` : `deg det FullN(X) ≤ |ι|` (needed for the `q^deg` clearing in `HasContent`);
* `Geometry.eval_fullPolyG` : `(fullPolyG).eval x = det (Full x)` (links the NV theorems, which are
  stated for `det Full(x)`, to `evalQ`);
* `hybPairFam_evalQ_ne` : non-vanishing of the family member is non-vanishing of `det Full(x)`.
-/

open Polynomial Finset Matrix

namespace CatalanCore.Rect

variable (Fr : Frame)

/-- Every entry of `FullN … X` in column `b` has degree `≤ 1` if `b` is a common node, else `0`. -/
theorem natDegree_fullN_entry_le {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (c : ι → ℕ) (xs ys : κ → ℕ) (a b : ι ⊕ κ) :
    ((FullN Fr c xs ys (X : ℚ[X])) a b).natDegree ≤ (if b.isLeft then 1 else 0) := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp [FullN, Blk, blkA, blkB, blkC, blkD, Matrix.fromBlocks, Matrix.one_apply]
  split_ifs <;> simp

/-- `deg det FullN(X) ≤ |ι|`. -/
theorem natDegree_fullN_le {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (c : ι → ℕ) (xs ys : κ → ℕ) :
    (FullN Fr c xs ys (X : ℚ[X])).det.natDegree ≤ Fintype.card ι := by
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun σ _ => ?_)
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ i, ((FullN Fr c xs ys (X : ℚ[X])) (σ i) i).natDegree
      ≤ ∑ i : ι ⊕ κ, (if i.isLeft then 1 else 0) :=
        Finset.sum_le_sum (fun i _ => natDegree_fullN_entry_le Fr c xs ys (σ i) i)
    _ = Fintype.card ι := by
        rw [Fintype.sum_sum_type]
        simp

/-- Evaluating `FullN … X` at `x` gives `FullN … x`. -/
theorem fullN_map_eval {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (c : ι → ℕ) (xs ys : κ → ℕ) (x : ℚ) :
    (Polynomial.evalRingHom x).mapMatrix (FullN Fr c xs ys (X : ℚ[X])) = FullN Fr c xs ys x := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [FullN, Blk, blkA, blkB, blkC, blkD, Matrix.fromBlocks, Matrix.one_apply]
  by_cases h : a = b <;> simp [h]

namespace Geometry

variable (G : Geometry)

theorem natDegree_fullPolyG_le : (G.fullPolyG Fr).natDegree ≤ G.C.card := by
  have := natDegree_fullN_le Fr (fun a : G.C => (a : ℕ)) G.xs G.ys
  simpa [fullPolyG, Geometry.Full] using this

theorem eval_fullPolyG (x : ℚ) : (G.fullPolyG Fr).eval x = (G.Full Fr x).det := by
  have h := (Polynomial.evalRingHom x).map_det (G.Full Fr (X : ℚ[X]))
  have e := fullN_map_eval Fr (fun a : G.C => (a : ℕ)) G.xs G.ys x
  simp only [Geometry.Full, Geometry.fullPolyG]
  unfold Geometry.Full at h
  rw [e] at h
  exact h

end Geometry

/-- The two-member hybrid family at slope `1/d`: members `(r, false)` = `after r (r/d)` and
`(r, true)` = `afterTop r (r/d)`, admissible when `d ∣ r`. -/
noncomputable def hybPairFam (d : ℕ) : PolyFamily where
  const := Fr.const
  ι := ℕ × Bool
  deg := fun n => n.1 + (if n.2 then 1 else 0)
  Adm := fun n => d ∣ n.1
  Q := fun n => if n.2 then (afterTop n.1 (n.1 / d)).fullPolyG Fr
    else (after n.1 (n.1 / d)).fullPolyG Fr

theorem hybPairFam_evalQ_false (d r : ℕ) (x : ℚ) :
    (hybPairFam Fr d).evalQ (r, false) x = (((after r (r / d)).Full Fr x).det) := by
  simp [hybPairFam, PolyFamily.evalQ, Geometry.eval_fullPolyG]

theorem hybPairFam_evalQ_true (d r : ℕ) (x : ℚ) :
    (hybPairFam Fr d).evalQ (r, true) x = (((afterTop r (r / d)).Full Fr x).det) := by
  simp [hybPairFam, PolyFamily.evalQ, Geometry.eval_fullPolyG]

theorem hybPairFam_Q_false (d r : ℕ) :
    (hybPairFam Fr d).Q (r, false) = Fr.fullPoly r (r / d) := by
  simp [hybPairFam, det_full_after]

/-- Either `after` or `afterTop` is a nonvanishing member, given that they do not both vanish. -/
theorem hybPairFam_exists_ne (d r : ℕ) (x : ℚ)
    (h : ¬ (((after r (r / d)).Full Fr x).det = 0 ∧ ((afterTop r (r / d)).Full Fr x).det = 0)) :
    ∃ b : Bool, (hybPairFam Fr d).evalQ (r, b) x ≠ 0 := by
  by_cases h1 : ((after r (r / d)).Full Fr x).det = 0
  · refine ⟨true, ?_⟩
    rw [hybPairFam_evalQ_true]
    intro h2; exact h ⟨h1, h2⟩
  · exact ⟨false, by rw [hybPairFam_evalQ_false]; exact h1⟩

end CatalanCore.Rect
