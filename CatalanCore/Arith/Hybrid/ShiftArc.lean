module
public import CatalanCore.Arith.Hybrid.ShiftFinal
@[expose] public section
open Finset
namespace CatalanCore.Arith.Hybrid
open ChainClasses

/-! # The arc condition at one node suffices

In a cut-free interval the residues move by `+1` without ever hitting the two singular residues
`0` and `h` (`4h = o`), so they stay on one side of `h`: if one node of the cell has a long residue
(outside the short arc), all nodes do.  This reduces `LongCell.hlong` to a single node. -/

section Arc
variable {p o : ℕ} [Fact p.Prime]

lemma mem_shortArc_iff {h : ℕ} (c : ZMod p) :
    c ∈ shortArc p h ↔ (if 2 * h < p then c.val < h else h ≤ c.val) := by
  classical
  simp [shortArc]

/-- One step: the next node is not singular, so the arc membership is preserved both ways. -/
lemma arc_step (hp : 5 ≤ p) {h : ℕ} (hh : h < p) (hroot : 4 * (h : ZMod p) = (o : ZMod p)) {r k : ℕ}
    (hstep : NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (k : ℤ) ((k + 1 : ℕ) : ℤ)) :
    (((k : ℕ) : ZMod p) ∈ shortArc p h ↔ ((k + 1 : ℕ) : ZMod p) ∈ shortArc p h) := by
  have hns : ¬ Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ)) ((k + 1 : ℕ) : ℤ) :=
    hstep _ (by push_cast; omega) (by push_cast; omega)
  have hsing : ¬ Singular (p : ℤ) (o : ℤ) ((k + 1 : ℕ) : ℤ) := fun hs => hns (Or.inl hs)
  unfold Singular at hsing
  push_neg at hsing
  obtain ⟨h1, h2⟩ := hsing
  have z1 : (((k + 1 : ℕ) : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h1
  have z2 : (4 * (((k + 1 : ℕ) : ℤ)) - (o : ℤ) : ℤ) ≠ 0 → True := fun _ => trivial
  have z2' : ((4 * (((k + 1 : ℕ) : ℤ)) - (o : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h2
  have h4 := four_ne_zmod p hp
  have hne_h : ((k + 1 : ℕ) : ZMod p) ≠ (h : ZMod p) := by
    intro he
    apply z2'
    push_cast at he ⊢
    rw [← hroot]
    linear_combination 4 * he
  have hz1 : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by simpa using z1
  set x : ZMod p := ((k : ℕ) : ZMod p) with hx
  have hk1 : ((k + 1 : ℕ) : ZMod p) = x + 1 := by rw [hx]; push_cast; ring
  rw [hk1] at hz1 hne_h ⊢
  have hv1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  have hvadd : (x + 1).val = (x.val + 1) % p := by rw [ZMod.val_add, hv1]
  have hxlt : x.val < p := ZMod.val_lt x
  have hne0 : (x.val + 1) % p ≠ 0 := by
    intro h0; apply hz1
    rw [← ZMod.val_eq_zero, hvadd]; exact h0
  have hlt : x.val + 1 < p := by
    by_contra hge
    have : x.val + 1 = p := by omega
    rw [this, Nat.mod_self] at hne0; exact hne0 rfl
  have hvx : (x + 1).val = x.val + 1 := by rw [hvadd, Nat.mod_eq_of_lt hlt]
  have hhv : (h : ZMod p).val = h := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hh]
  have hneh : (x + 1).val ≠ h := by
    intro he; apply hne_h
    apply ZMod.val_injective
    rw [he, hhv]
  rw [mem_shortArc_iff, mem_shortArc_iff, hvx]
  rw [hvx] at hneh
  by_cases h2 : 2 * h < p
  · simp only [h2, if_true]; omega
  · simp only [h2, if_false]; omega

/-- **One long node makes the whole cell long.** -/
theorem long_of_node (hp : 5 ≤ p) {h : ℕ} (hh : h < p) (hroot : 4 * (h : ZMod p) = (o : ZMod p))
    {r lo hi : ℕ}
    (hcut : ∀ x y : ℕ, lo ≤ x → x < hi → lo ≤ y → y < hi →
      NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (min (x : ℤ) y) (max (x : ℤ) y))
    {k0 : ℕ} (hk0 : lo ≤ k0 ∧ k0 < hi) (hl0 : ((k0 : ℕ) : ZMod p) ∉ shortArc p h) :
    ∀ k, lo ≤ k → k < hi → ((k : ℕ) : ZMod p) ∉ shortArc p h := by
  have step : ∀ k, lo ≤ k → k + 1 < hi →
      (((k : ℕ) : ZMod p) ∈ shortArc p h ↔ ((k + 1 : ℕ) : ZMod p) ∈ shortArc p h) := by
    intro k hk1 hk2
    apply arc_step hp hh hroot (r := r)
    have := hcut k (k + 1) hk1 (by omega) (by omega) hk2
    rwa [min_eq_left (by push_cast; omega), max_eq_right (by push_cast; omega)] at this
  have up : ∀ d, k0 + d < hi → ((k0 + d : ℕ) : ZMod p) ∉ shortArc p h := by
    intro d
    induction d with
    | zero => intro _; simpa using hl0
    | succ d ih =>
      intro hd hmem
      exact ih (by omega) ((step (k0 + d) (by omega) (by omega)).2 (by simpa [add_assoc] using hmem))
  have down : ∀ d, d ≤ k0 - lo → ((k0 - d : ℕ) : ZMod p) ∉ shortArc p h := by
    intro d
    induction d with
    | zero => intro _; simpa using hl0
    | succ d ih =>
      intro hd hmem
      have e : k0 - d = (k0 - (d + 1)) + 1 := by omega
      apply ih (by omega)
      rw [e]
      exact (step (k0 - (d + 1)) (by omega) (by omega)).1 hmem
  intro k hk1 hk2
  rcases le_total k0 k with hle | hle
  · have := up (k - k0) (by omega)
    rwa [show k0 + (k - k0) = k by omega] at this
  · have := down (k0 - k) (by omega)
    rwa [show k0 - (k0 - k) = k by omega] at this

end Arc

namespace LongCell
variable {p o r m h : ℕ} [Fact p.Prime]

/-- Build a long cell from a cut-free interval, a row node, and ONE long node (the arc condition
at a single node implies it everywhere, `long_of_node`). -/
def ofNode (hp : 5 ≤ p) (hh : h < p) (hroot : 4 * (h : ZMod p) = (o : ZMod p)) (lo hi : ℕ)
    (hra : r ≤ lo) (hhi : hi ≤ r + 2 * m)
    (hcut : ∀ x y : ℕ, lo ≤ x → x < hi → lo ≤ y → y < hi →
      NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (min (x : ℤ) y) (max (x : ℤ) y))
    (z0 : Fin m) (hz0 : lo ≤ r + 2 * z0.val ∧ r + 2 * z0.val < hi) (k0 : ℕ)
    (hk0 : lo ≤ k0 ∧ k0 < hi) (hl0 : ((k0 : ℕ) : ZMod p) ∉ shortArc p h) : LongCell p o r m h where
  lo := lo
  hi := hi
  hra := hra
  hhi := hhi
  hcut := hcut
  z0 := z0
  hz0 := hz0
  hlong := fun k hk1 hk2 _ _ => long_of_node hp hh hroot hcut hk0 hl0 k hk1 hk2

end LongCell

namespace LongCell
variable {p o r m h : ℕ} [Fact p.Prime] {Fr : Frame}

/-- The number of uncovered short residues is at most the size of the short arc. -/
theorem B_le_card_shortArc (c : LongCell p o r m h) : c.B ≤ (shortArc p h).card := by
  classical
  unfold B zoneSb
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- **Row theorem with any upper bound `B'` (`B ≤ B' ≤ p`) for the uncovered count**: enlarge the set
of uncovered short residues; the zero pattern only needs a superset. -/
theorem row_both_le (c : LongCell p o r m h) (I : HybInst Fr) [I.DiagOK r m] (hL : LamData Fr o)
    (hp : 5 ≤ p) (hm : 2 * m < p) (hN : 4 * (r + 2 * m + 1) < p * p) {k : ℕ}
    (hk : (4 : ZMod p) * k = (o : ZMod p)) (hb : p ≤ r + 2 * m)
    (hh : h < p) (hroot : 4 * (h : ZMod p) = (o : ZMod p)) {B' : ℕ} (hB : c.B ≤ B') (hBp : B' ≤ p)
    (hσ : c.sigma + (c.sigma - B') ≤ m) :
    GLE p (m - (c.sigma + (c.sigma - B')) + 2 * r) (Fr.fullPoly r m) ∧
    GLE p (m - (c.sigma + (c.sigma - B')) + topC I r m p + 2 * r)
      ((Rect.afterTop r m).fullPolyG Fr) := by
  classical
  obtain ⟨sb, hsub, hcard⟩ := Finset.exists_superset_card_eq (s := zoneSb p r m h) (n := B')
    (by simpa [LongCell.B] using hB) (by simpa [ZMod.card] using hBp)
  obtain ⟨α, β, hwt⟩ := weightedSameCell_zone hL hp hm (by omega) hk hh hroot c.hcut c.z0 c.hz0 c.hlong
  have hz0' := zoneZero_of_response hL hp hm (by omega) hh hroot c.hcut c.z0 c.hz0 c.hlong α β
  have hz : ChainModel.ZoneZero p r m (cellRows r m c.lo c.hi) (cellCols r m c.lo c.hi)
      (zoneWeight Fr p o r h (r + 2 * c.z0.val) α β) sb := fun cc hcc => hz0' cc (fun hs => hcc (hsub hs))
  have hcard2 := card_cellRows_add_cellCols (r := r) (m := m) c.hra c.hhi (a := c.lo) (b := c.hi)
  have H1 := ChainModel.twoLevel_fullPoly_gle_of_wt (Fr := Fr) hL hp hm (by omega) hk
    (cellRows r m c.lo c.hi) (cellCols r m c.lo c.hi) _ sb (zoneCell_of_cut c.hcut) hwt hz
  have H2 := ChainModel.twoLevel_top_gle_of_wt I hL hp hm hN hk hb
    (cellRows r m c.lo c.hi) (cellCols r m c.lo c.hi) _ sb (zoneCell_of_cut c.hcut) hwt hz
    (by rw [hcard2, hcard]; exact hσ)
  rw [hcard2, hcard] at H1 H2
  exact ⟨H1, H2⟩

end LongCell

#print axioms CatalanCore.Arith.Hybrid.long_of_node
#print axioms CatalanCore.Arith.Hybrid.LongCell.row_both_le
end CatalanCore.Arith.Hybrid
