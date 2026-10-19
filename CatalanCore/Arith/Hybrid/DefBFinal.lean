module

public import CatalanCore.Arith.Hybrid.DefBSchur

@[expose] public section

/-!
# Theorem B for a λ-like frame, at a prime `r < p < r + m`

`defAt_B_lam` : the additive deficit `m - (p - r) = r + m - p` at the prime `p`, relative to any
weights `(u, v)` that are tropically optimal for `hybW` (hypothesis `hopt`).  Everything else
(entries of `Full(X)` reduce to the block matrix `B̄`, the scalar Schur complement, the shape of the
zone rows, the rank count) is proved in `LamEntries`, `DefBLam`, `DefBSchur`, `DefB`, `DefBC5`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime] {r m j k : ℕ}

lemma Tfull_zone (S : BSetup p r m j k) {z w : ℕ} (hz : r ≤ z) (hw : w < k) :
    Tfull p j k z w = if z < p then (16 * ((z : ZMod p) - w))⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹))
      else if z - w = p then (16 : ZMod p)⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹) + 1) else 0 := by
  have := S.hkr
  have hwz : w < z := by omega
  unfold Tfull TB
  rw [if_neg (by omega), if_pos hwz, if_neg (by omega), if_pos hw]

lemma card_blk (r k : ℕ) : Fintype.card (Blk0 r k) + Fintype.card (Blk1 r k) = r := by
  have := Fintype.card_congr (Equiv.sumCompl (fun c : Fin r => (c : ℕ) < k))
  rw [Fintype.card_sum, Fintype.card_fin] at this
  exact this

/-- The shape of a zone row/column `z ≥ r` against `w ∈ B0` (generic in the label `z`). -/
lemma zone_shape (S : BSetup p r m j k) {d : ℕ} (hd : d = p - r) (hd0 : 0 < d) {z : ℕ}
    (hz : r ≤ z) (hzN : z < r + 2 * m) (w : Blk0 r k)
    (cz : Blk0 r k) (hcz : z < p ∨ (cz.1.val = z - p)) :
    rfC p (Tfull p j k z w.1.val) =
      if z < p then -(rfC p (-(4 * ((j : ℕ) : ZMod p))⁻¹)) *
          EL p r k d w ⟨(p - z - 1) % d, Nat.mod_lt _ hd0⟩
      else if w = cz then rfC p ((16 : ZMod p)⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹) + 1)) else 0 := by
  have hp5 := S.p5
  have h4 := four_ne_zmod p hp5
  rw [Tfull_zone S hz w.2]
  by_cases hlow : z < p
  · rw [if_pos hlow, if_pos hlow]
    have hmod : (p - z - 1) % d = p - z - 1 := Nat.mod_eq_of_lt (by omega)
    simp only [EL, Matrix.of_apply, hmod]
    have hcast : ((p - z - 1 + 1 : ℕ) : ZMod p) = -((z : ℕ) : ZMod p) := by
      have : p - z - 1 + 1 = p - z := by omega
      rw [this, Nat.cast_sub (by omega), ZMod.natCast_self]; ring
    rw [hcast]
    have : -(rfC p (-(4 * ((j : ℕ) : ZMod p))⁻¹)) *
        rfC p ((((w.1 : ℕ) : ZMod p) + -((z : ℕ) : ZMod p))⁻¹) =
        rfC p ((4 * ((j : ℕ) : ZMod p))⁻¹ * (((w.1 : ℕ) : ZMod p) + -((z : ℕ) : ZMod p))⁻¹) := by
      simp only [rfC_eq, map_mul, map_neg]; ring
    rw [this]
    congr 1
    have h16 : (16 : ZMod p) ≠ 0 := by
      have : (16 : ZMod p) = 4 * 4 := by norm_num
      rw [this]; exact mul_ne_zero h4 h4
    have : ((w.1 : ℕ) : ZMod p) + -((z : ℕ) : ZMod p) = -(((z : ℕ) : ZMod p) - ((w.1 : ℕ) : ZMod p)) := by
      ring
    rw [this, inv_neg, mul_inv, mul_inv]
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]
    field_simp
  · rw [if_neg hlow, if_neg hlow]
    have hczv : cz.1.val = z - p := hcz.resolve_left hlow
    by_cases hw : w = cz
    · have : z - (w.1 : ℕ) = p := by
        have := congrArg (fun t : Blk0 r k => t.1.val) hw
        have hw2 := w.2
        omega
      rw [if_pos this, if_pos hw]
    · have : ¬ z - (w.1 : ℕ) = p := by
        intro h
        apply hw
        apply Subtype.ext; apply Fin.ext
        omega
      rw [if_neg this, if_neg hw, rfC_zero]

end

end CatalanCore.Arith.Hybrid
