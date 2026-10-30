module

public import CatalanCore.Arith.Hybrid.Pieces

@[expose] public section

/-! # Raising a weight to an already budgeted piece

On one piece, replace a weight by its maximum with that piece's own affine
majorant.  Covers on disjoint pieces are preserved, so the integral budget
does not change.  The optional predicate selects residue classes.
-/

open Finset
namespace CatalanCore.Arith.Hybrid

noncomputable def patchPiece (active : ℕ→Prop) (r : ℕ) (P : Piece)
    (w : ℕ→ℝ) (p : ℕ) : ℝ := by
  classical
  exact if active p ∧ ⌊P.s*r⌋₊<p ∧ p≤⌊P.t*r⌋₊ then
    max (w p) (P.α*r+P.β*p+P.C) else w p

theorem le_patchPiece (active : ℕ→Prop) (r : ℕ) (P : Piece) (w : ℕ→ℝ) (p : ℕ) :
    w p≤patchPiece active r P w p := by
  classical
  unfold patchPiece
  split_ifs
  · exact le_max_left _ _
  · rfl

theorem bound_le_patchPiece (active : ℕ→Prop) (r : ℕ) (P : Piece) (w : ℕ→ℝ)
    {p : ℕ} (ha : active p) (hlo : ⌊P.s*r⌋₊<p) (hhi : p≤⌊P.t*r⌋₊) :
    P.α*r+P.β*p+P.C≤patchPiece active r P w p := by
  classical
  unfold patchPiece
  rw [if_pos ⟨ha,hlo,hhi⟩]
  exact le_max_right _ _

theorem Covers.patch_self {M : ℕ} {c : ZMod M} {w : ℕ→ℝ} {r : ℕ} {P : Piece}
    (h : Covers c w r P) (active : ℕ→Prop) : Covers c (patchPiece active r P w) r P := by
  classical
  intro p hlo hhi hp hc
  unfold patchPiece
  split_ifs
  · exact max_le (h p hlo hhi hp hc) le_rfl
  · exact h p hlo hhi hp hc

theorem Covers.patch_disjoint {M : ℕ} {c : ZMod M} {w : ℕ→ℝ} {r : ℕ} {P Q : Piece}
    (h : Covers c w r Q) (active : ℕ→Prop) (hd : P.t≤Q.s ∨ Q.t≤P.s) :
    Covers c (patchPiece active r P w) r Q := by
  classical
  intro p hlo hhi hp hc
  have hn : ¬(active p ∧ ⌊P.s*r⌋₊<p ∧ p≤⌊P.t*r⌋₊) := by
    rintro ⟨_,hlo',hhi'⟩
    rcases hd with hd | hd
    · have hh := Nat.floor_le_floor (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg r))
      omega
    · have hh := Nat.floor_le_floor (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg r))
      omega
  simpa only [patchPiece, if_neg hn] using h p hlo hhi hp hc

theorem Covers.patch_inactive {M : ℕ} {c : ZMod M} {w : ℕ→ℝ} {r : ℕ} {P Q : Piece}
    (h : Covers c w r Q) (active : ℕ→Prop)
    (ha : ∀p : ℕ, p.Prime → (p : ZMod M)=c → ¬active p) :
    Covers c (patchPiece active r P w) r Q := by
  classical
  intro p hlo hhi hp hc
  have hn : ¬(active p ∧ ⌊P.s*r⌋₊<p ∧ p≤⌊P.t*r⌋₊) := fun h => ha p hp hc h.1
  simpa only [patchPiece, if_neg hn] using h p hlo hhi hp hc

theorem Covers.patch_compatible {M : ℕ} {c : ZMod M} {w : ℕ→ℝ} {r : ℕ} {P Q : Piece}
    (h : Covers c w r Q) (active : ℕ→Prop) (hc : Q=P ∨ P.t≤Q.s ∨ Q.t≤P.s) :
    Covers c (patchPiece active r P w) r Q := by
  rcases hc with rfl | hc
  · exact h.patch_self active
  · exact h.patch_disjoint active hc

theorem patchPiece_eq_of_le_start (active : ℕ→Prop) (r : ℕ) (P : Piece)
    (w : ℕ→ℝ) {p : ℕ} (hp : p≤⌊P.s*r⌋₊) : patchPiece active r P w p=w p := by
  classical
  unfold patchPiece
  rw [if_neg (by omega)]

theorem patchPiece_eq_of_gt_end (active : ℕ→Prop) (r : ℕ) (P : Piece)
    (w : ℕ→ℝ) {p : ℕ} (hp : ⌊P.t*r⌋₊<p) : patchPiece active r P w p=w p := by
  classical
  unfold patchPiece
  rw [if_neg (by omega)]

end CatalanCore.Arith.Hybrid
