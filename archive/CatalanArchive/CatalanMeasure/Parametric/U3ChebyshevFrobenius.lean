module
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.Polynomial.Dickson
public import Mathlib.FieldTheory.Finite.Basic
@[expose] public section

/-!
# The Chebyshev Frobenius reflection identity

In characteristic `p` (odd prime), with `h = (p+1)/2`,
`T_{p-m} = X^p T_m - (X^2-1)^h U_{m-1}` for every integer `m`.
This is the algebraic core of identity K in Lemma U3.
-/

namespace CatalanMeasure.Parametric
open Polynomial
noncomputable section

section
variable (p : ℕ) [hp : Fact p.Prime]

theorem zmod_two_ne_zero (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h2p : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2p)

theorem zmod_chebyshev_T_prime (hp2 : p ≠ 2) :
    Chebyshev.T (ZMod p) (p : ℤ) = X ^ p := by
  have h2 := zmod_two_ne_zero p hp2
  have : Invertible (2 : ZMod p) := invertibleOfNonzero h2
  have hd := dickson_one_one_charP (ZMod p) p
  have := chebyshev_T_eq_dickson_one_one (R := ZMod p) p
  rw [this, hd]
  have h2p : (2 : ZMod p) ^ p = 2 := ZMod.pow_card 2
  have hc : (Polynomial.C (⅟(2 : ZMod p)) * Polynomial.C (2 : ZMod p) : (ZMod p)[X]) = 1 := by
    rw [← Polynomial.C_mul, invOf_mul_self, Polynomial.C_1]
  calc Polynomial.C (⅟(2 : ZMod p)) * ((X ^ p : (ZMod p)[X]).comp (2 * X))
      = Polynomial.C (⅟(2 : ZMod p)) * (Polynomial.C ((2 : ZMod p) ^ p) * X ^ p) := by
        rw [X_pow_comp, mul_pow, ← Polynomial.C_ofNat, ← Polynomial.C_pow]
    _ = X ^ p := by
        rw [h2p, ← mul_assoc, hc, one_mul]

/-- Pell identity for the Chebyshev pair, over any commutative ring. -/
theorem chebyshev_pell (R : Type*) [CommRing R] (n : ℕ) :
    Chebyshev.T R (n : ℤ) ^ 2 - (X ^ 2 - 1) * Chebyshev.U R ((n : ℤ) - 1) ^ 2 = 1 := by
  induction n with
  | zero => simp [Chebyshev.T_zero, Chebyshev.U_neg_one]
  | succ n ih =>
    have h1 := Chebyshev.T_eq_X_mul_T_sub_pol_U R ((n : ℤ) - 1)
    have h2 := Chebyshev.U_eq_X_mul_U_add_T R ((n : ℤ) - 1)
    have e1 : (n : ℤ) - 1 + 2 = (n : ℤ) + 1 := by ring
    have e2 : (n : ℤ) - 1 + 1 = (n : ℤ) := by ring
    rw [e1, e2] at h1
    rw [e2] at h2
    push_cast
    rw [show (n : ℤ) + 1 - 1 = n by ring, h1, h2]
    linear_combination ih

theorem zmod_chebyshev_U_prime (hp2 : p ≠ 2) :
    Chebyshev.U (ZMod p) ((p : ℤ) - 1) = (X ^ 2 - 1) ^ ((p - 1) / 2) := by
  have : NeZero (2 : ZMod p) := ⟨zmod_two_ne_zero p hp2⟩
  have hT := zmod_chebyshev_T_prime p hp2
  have hpell := chebyshev_pell (ZMod p) p
  rw [hT] at hpell
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hne : (X ^ 2 - 1 : (ZMod p)[X]) ≠ 0 := by
    intro h
    have := congrArg (fun q : (ZMod p)[X] => q.eval 0) h
    simp at this
  have hfrob : ((X ^ 2 - 1 : (ZMod p)[X])) ^ p = X ^ (2 * p) - 1 := by
    rw [sub_pow_char, ← pow_mul, one_pow]
  have hsq : (Chebyshev.U (ZMod p) ((p : ℤ) - 1)) ^ 2 = ((X ^ 2 - 1) ^ ((p - 1) / 2)) ^ 2 := by
    have h1 : (X ^ 2 - 1 : (ZMod p)[X]) * Chebyshev.U (ZMod p) ((p : ℤ) - 1) ^ 2 =
        (X ^ 2 - 1) * (X ^ 2 - 1) ^ (p - 1) := by
      have : (X ^ 2 - 1 : (ZMod p)[X]) * (X ^ 2 - 1) ^ (p - 1) = (X ^ 2 - 1) ^ p := by
        rw [← pow_succ' (X ^ 2 - 1 : (ZMod p)[X]) (p - 1), Nat.sub_add_cancel hp.out.one_le]
      rw [this, hfrob]
      have e : ((X : (ZMod p)[X]) ^ p) ^ 2 = X ^ (2 * p) := by ring
      rw [e] at hpell
      linear_combination -hpell
    have h2 := mul_left_cancel₀ hne h1
    rw [h2, ← pow_mul]
    congr 1
    omega
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · exfalso
    have hl := congrArg leadingCoeff h
    have hL : (Chebyshev.U (ZMod p) ((p : ℤ) - 1)).leadingCoeff = 1 := by
      have := Chebyshev.leadingCoeff_U_natCast (ZMod p) (p - 1)
      have hc : (((p - 1 : ℕ)) : ℤ) = (p : ℤ) - 1 := by
        have := hp.out.one_le; omega
      rw [hc] at this
      rw [this]
      exact ZMod.pow_card_sub_one_eq_one (zmod_two_ne_zero p hp2)
    have hm : (X ^ 2 - 1 : (ZMod p)[X]).Monic := by
      simpa using monic_X_pow_sub_C (1 : ZMod p) (show 2 ≠ 0 by norm_num)
    have hM : ((X ^ 2 - 1 : (ZMod p)[X]) ^ ((p - 1) / 2)).Monic := hm.pow _
    rw [hL, leadingCoeff_neg, hM.leadingCoeff] at hl
    have : (2 : ZMod p) = 0 := by linear_combination hl
    exact zmod_two_ne_zero p hp2 this

/-- `T_{p-m} = X^p T_m - (X^2-1)^{(p+1)/2} U_{m-1}` in characteristic `p`. -/
theorem zmod_chebyshev_reflect (hp2 : p ≠ 2) (m : ℤ) :
    Chebyshev.T (ZMod p) ((p : ℤ) - m) =
      X ^ p * Chebyshev.T (ZMod p) m - (X ^ 2 - 1) ^ ((p + 1) / 2) *
        Chebyshev.U (ZMod p) (m - 1) := by
  have hT := zmod_chebyshev_T_prime p hp2
  have hU := zmod_chebyshev_U_prime p hp2
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hh : (p + 1) / 2 = (p - 1) / 2 + 1 := by omega
  set G : ℤ → (ZMod p)[X] := fun m =>
    X ^ p * Chebyshev.T (ZMod p) m - (X ^ 2 - 1) ^ ((p + 1) / 2) *
        Chebyshev.U (ZMod p) (m - 1) - Chebyshev.T (ZMod p) ((p : ℤ) - m) with hG
  have hrec : ∀ m : ℤ, G (m + 2) = 2 * X * G (m + 1) - G m := by
    intro m
    have t1 := Chebyshev.T_add_two (ZMod p) m
    have u1 := Chebyshev.U_add_two (ZMod p) (m - 1)
    have t3 := Chebyshev.T_sub_two (ZMod p) ((p : ℤ) - m)
    rw [show m - 1 + 2 = m + 1 by ring, show m - 1 + 1 = m by ring] at u1
    have e1 : (p : ℤ) - (m + 2) = (p : ℤ) - m - 2 := by ring
    have e2 : (p : ℤ) - (m + 1) = (p : ℤ) - m - 1 := by ring
    have e3 : m + 1 - 1 = m := by ring
    have e4 : m + 2 - 1 = m + 1 := by ring
    simp only [hG, e1, e2, e3, e4]
    linear_combination (X ^ p : (ZMod p)[X]) * t1 - (X ^ 2 - 1) ^ ((p + 1) / 2) * u1 - t3
  have h0 : G 0 = 0 := by
    simp [hG, hT, Chebyshev.T_zero, Chebyshev.U_neg_one]
  have h1 : G 1 = 0 := by
    have a1 := Chebyshev.T_eq_X_mul_T_sub_pol_U (ZMod p) ((p : ℤ) - 1)
    have a2 := Chebyshev.T_sub_one (ZMod p) (p : ℤ)
    rw [show (p : ℤ) - 1 + 2 = (p : ℤ) + 1 by ring,
      show (p : ℤ) - 1 + 1 = (p : ℤ) by ring] at a1
    rw [hT] at a1 a2
    rw [hU] at a1
    simp only [hG, Chebyshev.T_one, Chebyshev.U_zero, sub_self, hh, pow_succ]
    linear_combination (-1 : (ZMod p)[X]) * a2 + a1
  have key : ∀ k : ℤ, G k = 0 := by
    intro k
    refine Chebyshev.induct (fun k => G k = 0) h0 h1 ?_ ?_ k
    · intro n h1' h0'
      have := hrec n
      simp only [h1', h0', mul_zero, sub_zero] at this
      exact this
    · intro n h0' h1'
      have := hrec (-(n : ℤ) - 1)
      rw [show -(n : ℤ) - 1 + 2 = -(n : ℤ) + 1 by ring,
        show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring] at this
      simp only [h0', h1', mul_zero, zero_sub] at this
      exact neg_eq_zero.mp this.symm
  have := key m
  simp only [hG] at this
  linear_combination -this

end
end
end CatalanMeasure.Parametric
