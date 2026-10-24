module
public import CatalanCore.Arith.Hybrid.ShiftData
public import CatalanCore.Arith.Hybrid.ChainWitnessFull
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

/-! # Member 1 of the two-level family, conditional on the weighted same-cell congruence

For the zone `xs i = r + 2 i`, `ys j = r + 2 j + 1` (`i, j < m`) of the original rectangular
matrix, `twoLevel_fullPoly_gle_of_wt` is the bound `Fr.fullPoly r m` receives from the Cauchy
data of the scaled Schur complement.  The two obligations that the frame side owes are the
hypotheses `hwt` (the weighted same-cell congruence N1) and `hzero` (the zero pattern of the
weight).  Everything else (integrality, the leading cross-cell blocks, the cell geometry, the
rescaling back to `Fr.fullPoly`) is proved here. -/

namespace ChainModel
open ChainClasses LemmaE

/-- The zone row nodes `r + 2 i`. -/
abbrev zoneX (r m : ℕ) : Fin m → ℕ := fun i => r + 2 * i.val
/-- The zone column nodes `r + 2 j + 1`. -/
abbrev zoneY (r m : ℕ) : Fin m → ℕ := fun j => r + 2 * j.val + 1

/-- The scaled Schur complement of the zone matrix. -/
noncomputable abbrev zoneT (Fr : Frame) (p r m : ℕ) [Fact p.Prime] : Matrix (Fin m) (Fin m) ℚ[X] :=
  Tscaled (Q Fr p r (zoneX r m) (zoneY r m)).det
    (full Fr p r (zoneX r m) (zoneY r m)).toBlocks₁₁ (full Fr p r (zoneX r m) (zoneY r m)).toBlocks₁₂
    (full Fr p r (zoneX r m) (zoneY r m)).toBlocks₂₁ (full Fr p r (zoneX r m) (zoneY r m)).toBlocks₂₂
    (Nm Fr p r (zoneX r m) (zoneY r m))

/-- The weighted same-cell congruence on `CR × CC` (the open obligation N1). -/
def ZoneWt (Fr : Frame) (p r m : ℕ) [Fact p.Prime] (CR CC : Finset (Fin m))
    (w : ZMod p → RatFunc (ZMod p)) : Prop :=
  ∀ z ∈ CR, ∀ y ∈ CC, ∃ T' : (LocRing p)[X], toQ p T' = zoneT Fr p r m z y ∧
    phiP p T' = ∑ c : ZMod p, rfC p ((c - ((zoneX r m z : ℕ) : ZMod p))⁻¹) * w c *
      rfC p ((c - ((zoneY r m y : ℕ) : ZMod p))⁻¹)

/-- The zero pattern of the weight. -/
def ZoneZero (p r m : ℕ) [Fact p.Prime] (CR CC : Finset (Fin m)) (w : ZMod p → RatFunc (ZMod p))
    (sb : Finset (ZMod p)) : Prop :=
  ∀ c, c ∉ sb → w c = 0 ∨ (∃ y, y ∉ CC ∧ ((zoneY r m y : ℕ) : ZMod p) = c) ∨
    (∃ z, z ∉ CR ∧ ((zoneX r m z : ℕ) : ZMod p) = c)

/-- Cell geometry: any two nodes of the cell are joined by a cut-free interval. -/
def ZoneCell (p o r m : ℕ) (CR CC : Finset (Fin m)) : Prop :=
  (∀ z ∈ CR, ∀ z' ∈ CR, zoneX r m z ≤ zoneX r m z' →
      NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (zoneX r m z : ℤ) (zoneX r m z' : ℤ)) ∧
  (∀ y ∈ CC, ∀ y' ∈ CC, zoneY r m y ≤ zoneY r m y' →
      NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (zoneY r m y : ℤ) (zoneY r m y' : ℤ))

variable {p r m o k : ℕ} [Fact p.Prime] {Fr : Frame}

omit [Fact p.Prime] in
lemma zoneX_lt (i : Fin m) : zoneX r m i < r + 2 * m := by have := i.isLt; simp only [zoneX]; omega
omit [Fact p.Prime] in
lemma zoneY_lt (i : Fin m) : zoneY r m i < r + 2 * m := by have := i.isLt; simp only [zoneY]; omega

lemma zone_residue_ne (hm : 2 * m < p) (i j : Fin m) : zoneX r m i % p ≠ zoneY r m j % p := by
  intro h
  have h1 : ((zoneX r m i : ℕ) : ZMod p) = ((zoneY r m j : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).2 h
  exact zone_dist_ne (r := r) hm i.isLt j.isLt (sub_eq_zero.2 h1.symm)

/-- The integrality of the zone Schur complement entries, `GLE p 1`. -/
theorem zoneT_gle_one (hL : LamData Fr o) (hp : 5 ≤ p) (hm : 2 * m < p) (hN : 4 * (r + 2 * m) < p * p)
    (hk : (4 : ZMod p) * k = (o : ZMod p)) (z y : Fin m) : GLE p 1 (zoneT Fr p r m z y) := by
  have H := T_entry_weighted (Fr := Fr) (p := p) (r := r) (N := r + 2 * m) (o := o) (k := k)
    (xs := zoneX r m) (ys := zoneY r m) hL hp hN (by omega) hk (fun z => zoneX_lt z)
    (fun y => zoneY_lt y) (fun z => by simp [zoneX]) (fun y => by simp only [zoneY]; omega)
    (fun z y => by simp only [zoneX, zoneY]; omega) (fun _ _ => 1) (fun _ _ => le_of_lt one_lt_two)
    (fun _ _ h => absurd h one_ne_zero) (fun z y _ => zone_residue_ne hm z y) z y
  exact H

/-- **Member 1, conditional on N1.**  The original zone determinant `Fr.fullPoly r m` has the
two-level bound `m - (σ + (σ - b)) + 2 r`, `σ = |CR| + |CC| - m`, `b = |sb|`. -/
theorem twoLevel_fullPoly_gle_of_wt (hL : LamData Fr o) (hp : 5 ≤ p) (hm : 2 * m < p)
    (hN : 4 * (r + 2 * m) < p * p) (hk : (4 : ZMod p) * k = (o : ZMod p))
    (CR CC : Finset (Fin m)) (w : ZMod p → RatFunc (ZMod p)) (sb : Finset (ZMod p))
    (hcell : ZoneCell p o r m CR CC) (hwt : ZoneWt Fr p r m CR CC w) (hzero : ZoneZero p r m CR CC w sb) :
    GLE p (m - ((CR.card + CC.card - m) + ((CR.card + CC.card - m) - sb.card)) + 2 * r)
      (Fr.fullPoly r m) := by
  classical
  have hr : r ≤ r + 2 * m := by omega
  have D := shiftData_of_wt (Fr := Fr) (p := p) (r := r) (N := r + 2 * m) (o := o) (k := k)
    (xs := zoneX r m) (ys := zoneY r m) hL hp hN hr hk (fun z => zoneX_lt z) (fun y => zoneY_lt y)
    CR CC w sb (fun z _ => by simp [zoneX]) (fun y _ => by simp only [zoneY]; omega) hcell.1 hcell.2
    (fun z y => zone_dist_ne (r := r) hm z.isLt y.isLt) hwt hzero
  have hint : ∀ z y, GLE p 1 (zoneT Fr p r m z y) := fun z y => zoneT_gle_one hL hp hm hN hk z y
  have H := gle_full_of_shiftData p (full Fr p r (zoneX r m) (zoneY r m)) (Q Fr p r (zoneX r m) (zoneY r m)).det
    (Q_primitive hL hp hN hr) (Nm Fr p r (zoneX r m) (zoneY r m)) (AN_eq p (fun _ : Fin r => 1) _)
    (2 * ∑ _i : Fin r, 1) (det_Atil p (fun _ : Fin r => 1) _).symm
    (fun z => ((zoneX r m z : ℕ) : ZMod p)) (fun y => ((zoneY r m y : ℕ) : ZMod p)) CR CC w sb hint D
  rw [full, det_rescale] at H
  have H2 := GLE.of_rescale H
  rw [← fullPoly_eq_fullN] at H2
  simpa [Fintype.card_fin] using H2

end ChainModel
#print axioms ChainModel.twoLevel_fullPoly_gle_of_wt
end CatalanCore.Arith.Hybrid
