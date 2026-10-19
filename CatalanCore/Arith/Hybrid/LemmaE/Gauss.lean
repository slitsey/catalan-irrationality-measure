module

public import CatalanCore.Arith.Hybrid.Tropical
public import Mathlib.RingTheory.Polynomial.GaussNorm
public import Mathlib.NumberTheory.Ostrowski

@[expose] public section

/-!
# Gauss norm bridge (Lemma E, T-route core, part 1)

`GLE p B f` ("all coefficients of `f` lie in `p^{-B} ℤ_(p)`") is the same as
`gn p f ≤ p^B` where `gn p` is Mathlib's Gauss norm for the `p`-adic absolute value
(`Polynomial.gaussNorm`).  Multiplicativity of the Gauss norm (`Polynomial.gaussNorm_mul`)
is the Gauss lemma, so `gn p (f * g) = gn p f * gn p g` gives all the valuation bookkeeping of
the T-route without a DVR or a residue field.
-/

open Polynomial CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid

variable (p : ℕ) [Fact p.Prime]

/-- The Gauss norm of a polynomial over `ℚ`: the maximum `p`-adic absolute value of the
coefficients. -/
noncomputable def gn (f : ℚ[X]) : ℝ := f.gaussNorm (Rat.AbsoluteValue.padic p) 1

lemma padic_isNonarch : IsNonarchimedean (Rat.AbsoluteValue.padic p) := by
  intro a b
  simp only [Rat.AbsoluteValue.padic_eq_padicNorm]
  exact_mod_cast padicNorm.nonarchimedean (p := p) (q := a) (r := b)

lemma gn_mul (f g : ℚ[X]) : gn p (f * g) = gn p f * gn p g :=
  Polynomial.gaussNorm_mul (v := Rat.AbsoluteValue.padic p) (c := 1) (padic_isNonarch p) one_pos f g

lemma gn_nonneg (f : ℚ[X]) : 0 ≤ gn p f :=
  Polynomial.gaussNorm_nonneg _ _ zero_le_one

lemma padic_coeff_le_gn (f : ℚ[X]) (i : ℕ) : (padicNorm p (f.coeff i) : ℝ) ≤ gn p f := by
  have := Polynomial.le_gaussNorm (Rat.AbsoluteValue.padic p) f zero_le_one i
  simpa [gn] using this

lemma gn_le_of_coeff {f : ℚ[X]} {C : ℝ} (_hC : 0 ≤ C) (h : ∀ i, (padicNorm p (f.coeff i) : ℝ) ≤ C) :
    gn p f ≤ C := by
  obtain ⟨i, hi⟩ := Polynomial.exists_eq_gaussNorm (Rat.AbsoluteValue.padic p) 1 f
  have : gn p f = (padicNorm p (f.coeff i) : ℝ) := by simpa [gn] using hi
  rw [this]; exact h i

lemma gn_C (x : ℚ) : gn p (C x) = padicNorm p x := by
  simp [gn]

/-- `x ∈ ℤ_(p)` iff `|x|_p ≤ 1`. -/
lemma mem_locRing_iff_padicNorm {x : ℚ} : x ∈ LocRing p ↔ padicNorm p x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx; simp [(LocRing p).zero_mem]
  have hden : x.den ≠ 0 := x.den_nz
  have hx' : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
  have hnorm : padicNorm p x = padicNorm p x.num / padicNorm p x.den := by
    conv_lhs => rw [hx']
    rw [padicNorm.div]
  have hden1 : (0 : ℚ) < padicNorm p x.den := by
    have := padicNorm.nonzero (p := p) (q := (x.den : ℚ)) (by exact_mod_cast hden)
    exact lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm this)
  rw [mem_locRing]
  constructor
  · intro hnd
    rw [hnorm]
    have h1 : padicNorm p x.den = 1 := (padicNorm.nat_eq_one_iff x.den).mpr hnd
    rw [h1, div_one]; exact padicNorm.of_int _
  · intro hle hd
    have hcop : ¬ (p : ℤ) ∣ x.num := by
      intro hn
      have hc := x.reduced
      have : p ∣ Nat.gcd x.num.natAbs x.den :=
        Nat.dvd_gcd (Int.natCast_dvd.mp hn) hd
      rw [hc] at this
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp this)
    have h1 : padicNorm p x.num = 1 := (padicNorm.int_eq_one_iff _).mpr hcop
    have h2 : padicNorm p x.den < 1 := (padicNorm.nat_lt_one_iff _).mpr hd
    rw [hnorm, h1] at hle
    have := (one_lt_div hden1).mpr h2
    linarith

/-- The key dictionary: `p^B * x ∈ ℤ_(p)` iff `|x|_p ≤ p^B`. -/
lemma pow_mul_mem_iff (B : ℕ) (x : ℚ) :
    (p : ℚ) ^ B * x ∈ LocRing p ↔ (padicNorm p x : ℝ) ≤ (p : ℝ) ^ B := by
  rw [mem_locRing_iff_padicNorm]
  have hv : ((padicNorm p ((p : ℚ) ^ B * x) : ℚ) : ℝ) =
      ((p : ℝ)⁻¹) ^ B * (padicNorm p x : ℝ) := by
    have h := map_mul (Rat.AbsoluteValue.padic p) ((p : ℚ) ^ B) x
    have h2 := map_pow (Rat.AbsoluteValue.padic p) (p : ℚ) B
    simp only [Rat.AbsoluteValue.padic_eq_padicNorm] at h h2
    have h3 : ((padicNorm p (p : ℚ) : ℚ) : ℝ) = (p : ℝ)⁻¹ := by
      rw [padicNorm.padicNorm_p_of_prime]; push_cast; rfl
    rw [h, h2, h3]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have : (padicNorm p ((p : ℚ) ^ B * x) ≤ 1) ↔ ((padicNorm p ((p : ℚ) ^ B * x) : ℚ) : ℝ) ≤ 1 := by
    exact_mod_cast Iff.rfl
  rw [this, hv, inv_pow, inv_mul_le_iff₀ (pow_pos hp0 B), mul_one]

/-- `GLE p B f` is the statement `gn p f ≤ p^B`. -/
lemma gle_iff_gn (B : ℕ) (f : ℚ[X]) : GLE p B f ↔ gn p f ≤ (p : ℝ) ^ B := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  constructor
  · intro h
    exact gn_le_of_coeff p (by positivity) fun i => (pow_mul_mem_iff p B _).mp (h i)
  · intro h i
    exact (pow_mul_mem_iff p B _).mpr ((padic_coeff_le_gn p f i).trans h)

lemma gn_one : gn p 1 = 1 := by
  rw [← C_1, gn_C]; simp

lemma gn_pow (f : ℚ[X]) (n : ℕ) : gn p (f ^ n) = gn p f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, gn_one]
  | succ k ih => rw [pow_succ, pow_succ, gn_mul, ih]

/-- Discreteness of the Gauss norm: `gn f < 1` forces `gn f ≤ 1/p`. -/
lemma gn_le_inv_of_lt_one {f : ℚ[X]} (h : gn p f < 1) : gn p f ≤ (p : ℝ)⁻¹ := by
  obtain ⟨i, hi⟩ := Polynomial.exists_eq_gaussNorm (Rat.AbsoluteValue.padic p) 1 f
  have e : gn p f = (padicNorm p (f.coeff i) : ℝ) := by simpa [gn] using hi
  rw [e] at h ⊢
  by_cases h0 : f.coeff i = 0
  · rw [h0]; simp
  · obtain ⟨z, hz⟩ := padicNorm.values_discrete (p := p) h0
    rw [hz] at h ⊢
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    push_cast at h ⊢
    have hz1 : 1 ≤ z := by
      by_contra hneg
      push_neg at hneg
      have : (1 : ℝ) ≤ (p : ℝ) ^ (-z) := one_le_zpow₀ hp1.le (by omega)
      linarith
    calc (p : ℝ) ^ (-z) ≤ (p : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hp1.le (by omega)
      _ = (p : ℝ)⁻¹ := zpow_neg_one _

end CatalanCore.Arith.Hybrid
