module

public import CatalanCore.Uniform.Content.Member.Transfer
public import CatalanCore.Arith.Hybrid.RankGLE

@[expose] public section

/-!
# Lemma LPD (lane H5): last-pole-cell savings for deletion members

Lemma R' and Lemma M of `lp-deletion-2026-10-27/THEOREM.md`, formalised for the member's OWN
matrix.  The data are the ones the proofs of LP1/LP2 (lane H3) produce for the FULL hybrid matrix:
feasible potentials `u, v` (`p^(u i + v j) · entry` is `p`-integral, as the integral lift `Bl`) and
a rank bound `rank (Bl mod p) + c ≤ n` for the reduction over `𝔽_p(X)`.  Then for every deletion
member:

* the restricted potentials are feasible and the reduction of the member is the submatrix of the
  reduction (`member_*`), so its rank is at most the rank of the full reduction;
* `lpd_member`: `GLE p (Σ_{retained} (u + v) - (c - k))`, `k = |C| - |S|` the number of deleted
  common nodes;
* `lpd_member_debit`: `GLE p ((Σ_full (u + v) - c) + k)`: the debit relative to the full-member
  price is at most `k` per prime.

No valuation of the full determinant is used; only the rank bound of the reduction (H3).
-/

open Polynomial Finset Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect

namespace CatalanCore.Uniform.Content.Member

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The member matrix is the principal restriction of the full hybrid matrix. -/
theorem fullN_member_eq_submatrix (Fr : Frame) (common : ι → ℕ) (xs ys : κ → ℕ) (S : Finset ι) :
    FullN Fr (fun a : S => common a.1) xs ys (X : ℚ[X]) =
      (FullN Fr common xs ys (X : ℚ[X])).submatrix (memberEmbedding S) (memberEmbedding S) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [memberEmbedding, FullN, Blk, blkA, blkB, blkC, blkD, Matrix.fromBlocks,
      Matrix.one_apply]

/-- **Lemma LPD (member form).** -/
theorem lpd_member (Fr : Frame) (common : ι → ℕ) (xs ys : κ → ℕ) (S : Finset ι)
    {p : ℕ} [Fact p.Prime] (u v : ι ⊕ κ → ℕ) (Bl : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X])
    (hB : ∀ i j, toQ p (Bl i j) =
      C ((p : ℚ) ^ (u i + v j)) * FullN Fr common xs ys (X : ℚ[X]) i j)
    (c : ℕ) (hrk : (Bl.map (phiP p)).rank + c ≤ Fintype.card (ι ⊕ κ)) :
    GLE p (∑ a : S ⊕ κ, u (memberEmbedding S a) + ∑ a : S ⊕ κ, v (memberEmbedding S a) -
        (c - (Fintype.card ι - S.card)))
      (FullN Fr (fun a : S => common a.1) xs ys (X : ℚ[X])).det := by
  set e := memberEmbedding (κ := κ) S with he
  rw [fullN_member_eq_submatrix]
  have hrank : ((Bl.submatrix e e).map (phiP p)).rank ≤ (Bl.map (phiP p)).rank := by
    have : (Bl.submatrix e e).map (phiP p) = (Bl.map (phiP p)).submatrix e e := rfl
    rw [this]
    exact Matrix.rank_submatrix_le _ _ _
  have hS : S.card ≤ Fintype.card ι := by simpa using Finset.card_le_univ S
  have hcard1 : Fintype.card (S ⊕ κ) = S.card + Fintype.card κ := by simp
  have hcard2 : Fintype.card (ι ⊕ κ) = Fintype.card ι + Fintype.card κ := by simp
  have hr0 := Matrix.rank_le_card_height ((Bl.submatrix e e).map (phiP p))
  exact gle_det_of_rank p ((FullN Fr common xs ys (X : ℚ[X])).submatrix e e) (Bl.submatrix e e)
    (fun a => u (e a)) (fun a => v (e a)) (fun i j => hB (e i) (e j))
    (c - (Fintype.card ι - S.card)) (by omega)

/-- **Lemma LPD, debit form.**  The member price exceeds the full-member price
`Σ (u + v) - c` by at most the number of deleted common nodes. -/
theorem lpd_member_debit (Fr : Frame) (common : ι → ℕ) (xs ys : κ → ℕ) (S : Finset ι)
    {p : ℕ} [Fact p.Prime] (u v : ι ⊕ κ → ℕ) (Bl : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X])
    (hB : ∀ i j, toQ p (Bl i j) =
      C ((p : ℚ) ^ (u i + v j)) * FullN Fr common xs ys (X : ℚ[X]) i j)
    (c : ℕ) (hrk : (Bl.map (phiP p)).rank + c ≤ Fintype.card (ι ⊕ κ)) :
    GLE p ((∑ a, u a + ∑ a, v a - c) + (Fintype.card ι - S.card))
      (FullN Fr (fun a : S => common a.1) xs ys (X : ℚ[X])).det := by
  have h := lpd_member Fr common xs ys S u v Bl hB c hrk
  refine h.mono ?_
  have h1 : ∑ a : S ⊕ κ, u (memberEmbedding S a) ≤ ∑ a, u a := by
    calc ∑ a : S ⊕ κ, u (memberEmbedding S a)
        = ∑ b ∈ Finset.univ.image (memberEmbedding (κ := κ) S), u b := by
          rw [Finset.sum_image]
          intro a _ b _ h
          exact (memberEmbedding (κ := κ) S).injective h
      _ ≤ ∑ a, u a := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have h2 : ∑ a : S ⊕ κ, v (memberEmbedding S a) ≤ ∑ a, v a := by
    calc ∑ a : S ⊕ κ, v (memberEmbedding S a)
        = ∑ b ∈ Finset.univ.image (memberEmbedding (κ := κ) S), v b := by
          rw [Finset.sum_image]
          intro a _ b _ h
          exact (memberEmbedding (κ := κ) S).injective h
      _ ≤ ∑ a, v a := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hS : S.card ≤ Fintype.card ι := by simpa using Finset.card_le_univ S
  omega

end CatalanCore.Uniform.Content.Member
