module
public import CatalanFrames.HybCommon.DeficitProfile.Arithmetic
public import CatalanCore.Arith.Hybrid.ShiftArc
@[expose] public section
open Finset CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon
open ChainClasses

/-! # Long cells of profile rows

The cell of a profile row is `[profileLeft, profileRight)`.  Its cut-freeness (`hcut`) follows from the
pole-pair data alone (`profile_row_cut_pair`, the `cert`-free form of `profile_row_cut`), so it also
serves the new two-level rows.  `longCellOfRow` assembles the `LongCell` of the two-level row theorem
from that and from the remaining row-specific facts (a row node in the cell, one long node). -/

lemma profile_class_mod_pair {o r p : ℕ} (ho : o=1 ∨ o=3) {P : DeficitRow}
    (ha : profileRowActive o r p P) :
    p%4=if P.poleClass=1 then 4-o else o := by
  have h:=congrArg ZMod.val ha.1
  have ho0 : 0<o := by rcases ho with rfl|rfl <;> omega
  have ho4 : o<4 := by rcases ho with rfl|rfl <;> omega
  by_cases ht : P.poleClass=1
  · simpa only [profileClass,if_pos ht,ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega : 4-o<4)] using h
  · simpa only [profileClass,if_neg ht,ZMod.val_natCast,
      Nat.mod_eq_of_lt ho4] using h

lemma profile_row_cut_pair {o r p : ℕ} (ho : o=1 ∨ o=3) {P : DeficitRow}
    (hclass : P.poleClass=1 ∨ P.poleClass=3) (hpair : PolePair P.poleClass P.A4 P.B4)
    (ha : profileRowActive o r p P) (hp : 5≤p) (hb : profileRight o r p P≤r+p) :
    ∀x y:ℕ,profileLeft o r p P≤x→x<profileRight o r p P→
      profileLeft o r p P≤y→y<profileRight o r p P→
      NoCut (Cut p r (Singular p o)) (min (x:ℤ) y) (max (x:ℤ) y) := by
  intro x y hax hxb hay hyb
  have ha0 : r≤profileLeft o r p P := le_max_left _ _
  have haA : poleCut p o P.A4≤profileLeft o r p P := le_max_right _ _
  have hbB : profileRight o r p P≤poleCut p o P.B4 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have H:=pole_pair_noCut ho hclass hp (profile_class_mod_pair ho ha) hpair
    (r:=r) (z:=min x y) (y:=max x y)
    (by omega) (by omega) (by omega) (by omega)
  simpa only [Nat.cast_min,Nat.cast_max] using H

/-- The `LongCell` of a profile row: `[profileLeft, profileRight)` with `m = r/8`, given a row node
in the cell and one long node (the arc condition at a single node, `long_of_node`). -/
noncomputable def longCellOfRow {o r p h : ℕ} [Fact p.Prime] (ho : o=1 ∨ o=3) {P : DeficitRow}
    (hclass : P.poleClass=1 ∨ P.poleClass=3) (hpair : PolePair P.poleClass P.A4 P.B4)
    (ha : profileRowActive o r p P) (hp : 5≤p) (hb : profileRight o r p P≤r+p)
    (hh : h < p) (hroot : 4 * (h : ZMod p) = (o : ZMod p))
    (z0 : Fin (r/8)) (hz0 : profileLeft o r p P ≤ r + 2 * z0.val ∧ r + 2 * z0.val < profileRight o r p P)
    (k0 : ℕ) (hk0 : profileLeft o r p P ≤ k0 ∧ k0 < profileRight o r p P)
    (hl0 : ((k0 : ℕ) : ZMod p) ∉ shortArc p h) : LongCell p o r (r/8) h :=
  LongCell.ofNode hp hh hroot (profileLeft o r p P) (profileRight o r p P) (le_max_left _ _)
    (min_le_left _ _) (profile_row_cut_pair ho hclass hpair ha hp hb) z0 hz0 k0 hk0 hl0

end CatalanFrames.HybCommon

#print axioms CatalanFrames.HybCommon.profile_row_cut_pair
#print axioms CatalanFrames.HybCommon.longCellOfRow
