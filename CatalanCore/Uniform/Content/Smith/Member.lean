module

public import CatalanCore.Uniform.Content.Smith.LP2

@[expose] public section

/-!
# Deletion transfer for rank witnesses (Lemma LPD), any index type

A `HasRankWit Fr p r m u v k` records the reduction `B̄` of `Full(X)` under the potentials `(u, v)`
with `rank B̄ + k ≤ r + m`.  For **any** finite index type `ι` with row and column maps
`ia, ib : ι → Fin r ⊕ Fin m` (member cores: delete rows and columns, or any sub-selection), the
submatrix `Φ_ι = (Full_{ia i, ib j})` satisfies

  `GLE p (Σ_i u(ia i) + Σ_j v(ib j) - (|ι| + k - (r + m))) (det Φ_ι)`,

because `rank (B̄.submatrix ia ib) ≤ rank B̄` (`Matrix.rank_submatrix_le`) and the scaled entries of the
submatrix are the corresponding scaled entries.  For `|ι| = r + m - s` this is the saving `k - s`
of Lemma LPD, with potentials restricted to the member.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix CatalanCore.Arith.Hybrid

namespace CatalanCore.Uniform.Content.Smith

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o r m j : ℕ} {u v : Fin r ⊕ Fin m → ℕ} {k : ℕ}

/-- **Deletion transfer (Lemma LPD) for rank witnesses.** -/
theorem _root_.CatalanCore.Arith.Hybrid.HasRankWit.gle_sub (h : HasRankWit Fr p r m u v k) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ia ib : ι → Fin r ⊕ Fin m) :
    GLE p (∑ i, u (ia i) + ∑ j, v (ib j) - (Fintype.card ι + k - (r + m)))
      (Matrix.of fun i j => fullEntry Fr r m (ia i) (ib j)).det := by
  classical
  obtain ⟨Bbar, hB, hrk⟩ := h
  choose g hg1 hg2 using hB
  let Bl : Matrix ι ι (LocRing p)[X] := Matrix.of fun i j => g (ia i) (ib j)
  have hmap : Bl.map (phiP p) = Bbar.submatrix ia ib := by
    ext i j; simp [Bl, hg2]
  have h1 : (Bbar.submatrix ia ib).rank ≤ Bbar.rank := Matrix.rank_submatrix_le Bbar ia ib
  have h2 : (Bbar.submatrix ia ib).rank ≤ Fintype.card ι := by
    simpa using Matrix.rank_le_card_width (Bbar.submatrix ia ib)
  refine gle_det_of_rank p (Matrix.of fun i j => fullEntry Fr r m (ia i) (ib j)) Bl
    (fun i => u (ia i)) (fun j => v (ib j)) (fun i j => hg1 (ia i) (ib j))
    (Fintype.card ι + k - (r + m)) ?_
  rw [hmap]
  omega

/-- LP2 for members of the hybrid family (any index type). -/
theorem LP2Hyp.gle_sub (H : LP2Hyp Fr p q o r m k j) (hpm : p < r + m) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ia ib : ι → Fin r ⊕ Fin m) :
    GLE p (∑ i, uPot p r k (Frame.hybRow r m (ia i)) + ∑ i, uPot p r k (Frame.hybCol r m (ib i)) -
        (Fintype.card ι + (m - (p - r)) - (r + m)))
      (Matrix.of fun i j => fullEntry Fr r m (ia i) (ib j)).det :=
  (H.gleAt hpm).gle_sub ia ib

end CatalanCore.Uniform.Content.Smith
