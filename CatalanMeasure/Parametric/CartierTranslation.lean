module

public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Algebra.Polynomial.Taylor
public import Lean.Elab.Tactic.Omega

/-!
# Translation of Cartier coefficient blocks

Translating the polynomial coordinate by one mixes only coefficients whose
lower base-p digit is p-1. This is a uniform algebraic foundation for studying
the additional rank loss of the column difference filter; no rank-loss or
irrationality-measure conclusion is asserted here.
-/

@[expose] public section

namespace CatalanMeasure.Parametric

set_option autoImplicit false

open Polynomial

theorem choose_cartier_digit (p n v : ℕ) [Fact p.Prime] :
    (n.choose (v * p + (p - 1)) : ZMod p) =
      if n % p = p - 1 then (n / p).choose v else 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hlow : p - 1 < p := by omega
  have hmod : (v * p + (p - 1)) % p = p - 1 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hlow]
  have hdiv : (v * p + (p - 1)) / p = v := by
    rw [Nat.add_comm, Nat.mul_comm v p, Nat.add_mul_div_left _ _ hp,
      Nat.div_eq_of_lt hlow, zero_add]
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (p := p) (n := n) (k := v * p + (p - 1))
  have hc := (ZMod.natCast_eq_natCast_iff _ _ p).mpr h
  rw [hmod, hdiv] at hc
  rw [hc, Nat.cast_mul]
  split_ifs with heq
  · simp [heq]
  · have hn : n % p < p - 1 := by
      have := Nat.mod_lt n hp
      omega
    simp [Nat.choose_eq_zero_of_lt hn]

theorem coeff_translate_one (p : ℕ) (F : (ZMod p)[X]) (k : ℕ) :
    (F.comp (X + 1)).coeff k =
      ∑ n ∈ F.support, F.coeff n * (n.choose k : ZMod p) := by
  rw [comp_eq_sum_left, Polynomial.sum_def, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro n hn
  rw [coeff_C_mul, coeff_X_add_one_pow]

theorem cartier_coeff_translate (p : ℕ) [Fact p.Prime]
    (F : (ZMod p)[X]) (v : ℕ) :
    (F.comp (X + 1)).coeff (v * p + (p - 1)) =
      ∑ n ∈ F.support,
        if n % p = p - 1 then F.coeff n * ((n / p).choose v : ZMod p) else 0 := by
  rw [coeff_translate_one]
  apply Finset.sum_congr rfl
  intro n hn
  rw [choose_cartier_digit]
  split_ifs <;> simp

theorem coeff_cartier_translate_lowDegree (p : ℕ) [Fact p.Prime]
    (F : (ZMod p)[X]) (hF : F.natDegree < 2 * p - 1) :
    (F.comp (X + 1)).coeff (p - 1) = F.coeff (p - 1) := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have ht := cartier_coeff_translate p F 0
  simp only [Nat.zero_mul, zero_add, Nat.choose_zero_right, Nat.cast_one, mul_one] at ht
  rw [ht]
  rw [Finset.sum_eq_single (p - 1)]
  · simp [Nat.mod_eq_of_lt (show p - 1 < p by omega)]
  · intro n hn hne
    have hnd : n < 2 * p - 1 :=
      lt_of_le_of_lt (le_natDegree_of_ne_zero (mem_support_iff.mp hn)) hF
    have hmod : n % p ≠ p - 1 := by
      intro heq
      have hd := Nat.mod_add_div n p
      rw [heq] at hd
      by_cases hquot : n / p = 0
      · simp only [hquot, Nat.mul_zero, Nat.add_zero] at hd
        exact hne hd.symm
      · have hq : 1 ≤ n / p := Nat.pos_of_ne_zero hquot
        have hprod := Nat.mul_le_mul_left p hq
        simp only [Nat.mul_one] at hprod
        omega
    simp [hmod]
  · intro hn
    have hz : F.coeff (p - 1) = 0 := by
      simpa only [mem_support_iff, not_not] using hn
    simp [hz]

theorem cartier_pairing_translate (p : ℕ) [Fact p.Prime]
    (Q C : (ZMod p)[X]) (hQ : Q.natDegree < p) (hC : C.natDegree < p) :
    ((Q.comp (X + 1)) * (C.comp (X + 1))).coeff (p - 1) =
      (Q * C).coeff (p - 1) := by
  have hd : (Q * C).natDegree ≤ Q.natDegree + C.natDegree := natDegree_mul_le
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hprod : (Q * C).natDegree < 2 * p - 1 := by omega
  simpa only [mul_comp] using coeff_cartier_translate_lowDegree p (Q * C) hprod

end CatalanMeasure.Parametric
