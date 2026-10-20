module

public import CatalanCore.Basic.ZModGood

@[expose] public section

open CatalanCore

namespace CatalanCore

/-- A reduced denominator divisible by `ℓ` but not by `ℓ²` gives a unit after
one multiplication by `ℓ`. No valuation API is needed. -/
lemma good_mul_of_den_dvd_not_sq {ℓ : ℕ} [Fact ℓ.Prime] (x : ℚ)
    (hdiv : ℓ ∣ x.den) (hsq : ¬ ℓ ^ 2 ∣ x.den) :
    ∃ u : ZMod ℓ, u ≠ 0 ∧ Good ℓ ((ℓ : ℚ) * x) u := by
  obtain ⟨d, hd⟩ := hdiv
  have hdn : ¬ ℓ ∣ d := by
    rintro ⟨k, hk⟩
    apply hsq
    refine ⟨k, ?_⟩
    rw [hd, hk]
    ring
  have hdz : (d : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hdn
  have hnz : (x.num : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hn
    have hn' : ℓ ∣ x.num.natAbs := Int.natCast_dvd.1 hn
    have hp : ℓ.Prime := Fact.out
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes x.reduced hn' ⟨d, hd⟩)
  refine ⟨(x.num : ZMod ℓ) / d, div_ne_zero hnz hdz, ?_⟩
  have g := (Good.intCast (ℓ := ℓ) x.num).div (Good.natCast d) hdz
  have hl0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hd0 : (d : ℚ) ≠ 0 := by
    have hdn : d ≠ 0 := by
      intro h
      rw [h, Nat.mul_zero] at hd
      exact x.den_ne_zero hd
    exact_mod_cast hdn
  have heq : (ℓ : ℚ) * x = (x.num : ℚ) / d := by
    calc
      (ℓ : ℚ) * x = (ℓ : ℚ) * ((x.num : ℚ) / x.den) := by rw [x.num_div_den]
      _ = (x.num : ℚ) / d := by rw [hd]; push_cast; field_simp
  exact g.congr' heq.symm

end CatalanCore
