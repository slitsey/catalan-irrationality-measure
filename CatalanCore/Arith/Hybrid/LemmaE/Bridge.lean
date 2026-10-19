module

public import CatalanCore.Arith.Hybrid.LemmaE.Cong
public import CatalanCore.Arith.Hybrid.LemmaE.Harmonic

@[expose] public section

/-!
# Bridge: congruence of constants = equality of reductions in `ZMod p`

For `x ∈ ℤ_(p)`, `red x = (x : ZMod p)` (Rat.cast; `x.den` is a unit).  `Cng (C x) (C y)` holds
iff `red x = red y` (`cng_C_iff`).  With this, every entry congruence of the T-route becomes an
identity in the finite field `ZMod p`, where the harmonic facts of `Harmonic.lean` live.
-/

open Polynomial CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid.LemmaE

variable (p : ℕ) [Fact p.Prime]

/-- Reduction of a `p`-integral rational mod `p`. -/
def red (x : ℚ) : ZMod p := (x : ZMod p)

variable {p}

lemma den_cast_ne_zero {x : ℚ} (hx : x ∈ LocRing p) : (x.den : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; exact hx

lemma red_add {x y : ℚ} (hx : x ∈ LocRing p) (hy : y ∈ LocRing p) :
    red p (x + y) = red p x + red p y :=
  Rat.cast_add_of_ne_zero (den_cast_ne_zero hx) (den_cast_ne_zero hy)

lemma red_mul {x y : ℚ} (hx : x ∈ LocRing p) (hy : y ∈ LocRing p) :
    red p (x * y) = red p x * red p y :=
  Rat.cast_mul_of_ne_zero (den_cast_ne_zero hx) (den_cast_ne_zero hy)

lemma red_neg (x : ℚ) : red p (-x) = - red p x := Rat.cast_neg x

lemma red_sub {x y : ℚ} (hx : x ∈ LocRing p) (hy : y ∈ LocRing p) :
    red p (x - y) = red p x - red p y := by
  rw [sub_eq_add_neg, red_add hx ((LocRing p).neg_mem hy), red_neg, ← sub_eq_add_neg]

lemma red_int (z : ℤ) : red p (z : ℚ) = (z : ZMod p) := Rat.cast_intCast z

/-- `|x|_p < 1` iff `x ≡ 0`. -/
lemma padicNorm_lt_one_iff {x : ℚ} (hx : x ∈ LocRing p) : padicNorm p x < 1 ↔ red p x = 0 := by
  by_cases h0 : x = 0
  · subst h0; simp [red]
  have hden : (x.den : ZMod p) ≠ 0 := den_cast_ne_zero hx
  have hxd : red p x = (x.num : ZMod p) / (x.den : ZMod p) := by
    unfold red; exact Rat.cast_def x
  have hnorm : padicNorm p x = padicNorm p x.num := by
    have e : padicNorm p x = padicNorm p x.num / padicNorm p x.den := by
      conv_lhs => rw [← Rat.num_div_den x]
      rw [padicNorm.div]
    have h1 : padicNorm p x.den = 1 := (padicNorm.nat_eq_one_iff x.den).mpr hx
    rw [e, h1, div_one]
  rw [hnorm, hxd, div_eq_zero_iff, or_iff_left hden, padicNorm.int_lt_one_iff,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Congruence of constants is equality of reductions. -/
theorem cng_C_iff {x y : ℚ} (hx : x ∈ LocRing p) (hy : y ∈ LocRing p) :
    Cng p (C x) (C y) ↔ red p x = red p y := by
  unfold Cng
  rw [← C_sub, gn_C]
  have h : padicNorm p (x - y) < 1 ↔ red p (x - y) = 0 :=
    padicNorm_lt_one_iff ((LocRing p).sub_mem hx hy)
  rw [red_sub hx hy, sub_eq_zero] at h
  rw [← h]
  exact_mod_cast Iff.rfl

end CatalanCore.Arith.Hybrid.LemmaE
