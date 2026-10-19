module

public import CatalanCore.Arith.Hybrid.Pieces

@[expose] public section

/-!
# Tools for piece tables with rational data

`mkPiece sn sd tn td A B E D` is the piece on `(sn/sd, tn/td]` with `α = A/D`, `β = B/D`,
`C = E/D`; the floors are `sn r / sd`, `tn r / td` (`floor_mk_s`, `floor_mk_t`) and the pointwise
bound follows from an integer inequality (`real_of_int_bound`), which `omega` proves.
-/

open Finset

namespace CatalanCore.Arith.Hybrid

/-- A piece with rational data. -/
noncomputable def mkPiece (sn sd tn td : ℕ) (A B E D : ℤ) : Piece :=
  ⟨(sn : ℝ) / sd, (tn : ℝ) / td, (A : ℝ) / D, (B : ℝ) / D, (E : ℝ) / D⟩

lemma floor_frac (a b r : ℕ) : ⌊((a : ℝ) / b) * r⌋₊ = a * r / b := by
  have : ((a : ℝ) / b) * r = ((a * r : ℕ) : ℝ) / b := by push_cast; ring
  rw [this, Nat.floor_div_eq_div]

lemma floor_mk_s (sn sd tn td : ℕ) (A B E D : ℤ) (r : ℕ) :
    ⌊(mkPiece sn sd tn td A B E D).s * r⌋₊ = sn * r / sd := floor_frac _ _ _

lemma floor_mk_t (sn sd tn td : ℕ) (A B E D : ℤ) (r : ℕ) :
    ⌊(mkPiece sn sd tn td A B E D).t * r⌋₊ = tn * r / td := floor_frac _ _ _

lemma real_of_int_bound {x r p : ℕ} (D A B E : ℤ) (hD : 0 < D)
    (key : D * (x : ℤ) ≤ A * r + B * p + E) :
    (x : ℝ) ≤ ((A : ℝ) / D) * r + ((B : ℝ) / D) * p + (E : ℝ) / D := by
  have h := (Int.cast_le (R := ℝ)).mpr key
  push_cast at h
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← add_div, le_div_iff₀ hD']
  linarith

lemma cls4_mod3 {p : ℕ} (h : (p : ZMod 4) = 3) : p % 4 = 3 := by
  have := (ZMod.natCast_eq_natCast_iff' p 3 4).mp (by simpa using h)
  omega

lemma cls4_mod1 {p : ℕ} (h : (p : ZMod 4) = 1) : p % 4 = 1 := by
  have := (ZMod.natCast_eq_natCast_iff' p 1 4).mp (by simpa using h)
  omega

end CatalanCore.Arith.Hybrid
