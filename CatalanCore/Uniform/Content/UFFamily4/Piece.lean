module

public import CatalanCore.Uniform.Content.UFFamily4.Output

@[expose] public section

/-!
# Discharging `UFBound` for a rational template piece (lane H, H13)

`ufbound_of_nat` reduces `UFBound depth (sa/sb) (ta/tb) (A/D) (B/D) (C/D)` to a statement in `ℕ`/`ℤ`
(one linear inequality per family region, with the two floors cleared), which `omega` closes after
unfolding `baseOf` (see `scripts/claude/bank/uf/piece.py`, which writes one such lemma per piece).
-/

open CatalanCore CatalanCore.Uniform.Content.UFFamily3

namespace CatalanCore.Uniform.Content.UFFamily4

theorem ufbound_of_nat {depth : ℕ} {sa sb ta tb D : ℕ} (hsb : 0 < sb) (htb : 0 < tb) (hD : 0 < D)
    (A B Cc : ℤ)
    (h : ∀ r p : ℕ, r % 2 = 0 → Band r p → sa * r < sb * p → tb * p ≤ ta * r →
      ∀ i, RegOf i r p → (D : ℤ) * ((baseOf i r p + depth : ℕ) : ℤ) ≤ A * r + B * p + Cc) :
    UFBound depth ((sa : ℝ) / sb) ((ta : ℝ) / tb) ((A : ℝ) / D) ((B : ℝ) / D) ((Cc : ℝ) / D) := by
  intro r p hr hb hs ht i hi
  have hsbR : (0 : ℝ) < sb := by exact_mod_cast hsb
  have htbR : (0 : ℝ) < tb := by exact_mod_cast htb
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hs' : ((sa : ℝ) / sb) * r < p := (Nat.floor_lt (by positivity)).1 hs
  have ht' : (p : ℝ) ≤ ((ta : ℝ) / tb) * r := (Nat.le_floor_iff (by positivity)).1 ht
  have hs2 : sa * r < sb * p := by
    have : (sa : ℝ) * r < sb * p := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hsbR] at hs'; linarith
    exact_mod_cast this
  have ht2 : tb * p ≤ ta * r := by
    have : (tb : ℝ) * p ≤ ta * r := by
      rw [div_mul_eq_mul_div, le_div_iff₀ htbR] at ht'; linarith
    exact_mod_cast this
  have key := h r p hr hb hs2 ht2 i hi
  have keyR : (D : ℝ) * (((baseOf i r p + depth : ℕ)) : ℝ) ≤ A * r + B * p + Cc := by
    exact_mod_cast key
  have e : (A : ℝ) / D * r + (B : ℝ) / D * p + (Cc : ℝ) / D = (A * r + B * p + Cc) / D := by
    field_simp
  rw [e, le_div_iff₀ hDR]
  linarith

end CatalanCore.Uniform.Content.UFFamily4
