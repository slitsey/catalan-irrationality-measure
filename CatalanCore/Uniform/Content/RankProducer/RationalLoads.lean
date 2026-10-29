import CatalanCore.Uniform.Content.RankProducer.Lines
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
open scoped Classical
variable (p : ℕ) [Fact p.Prime]

/-- Large fixed primes are units for a recorded rational denominator, without factoring it. -/
theorem rational_mem_of_den_lt (q : ℚ) (hq : q.den < p) : q ∈ S p := by
  intro hd
  have hle := Nat.le_of_dvd q.den_pos hd
  omega

/-- Rational unit witnesses retain their nonzero reduction. -/
theorem rational_red_ne_zero (q : ℚ) (hq0 : q ≠ 0)
    (hq : q ∈ S p) (hi : q⁻¹ ∈ S p) : red p q ≠ 0 := by
  have hmul := (good_red hq).mul (good_red hi)
  have he : red p q * red p q⁻¹ = 1 := by
    rw [← hmul.eq, mul_inv_cancel₀ hq0, (Good.one (ℓ := p)).eq]
  intro hz
  rw [hz, zero_mul] at he
  exact zero_ne_one he

/-- Exact rational orthogonality survives reduction in the ambient function field. -/
theorem castV_omega_eq_zero (v w : ℚ × ℚ)
    (hv1 : v.1 ∈ S p) (hv2 : v.2 ∈ S p)
    (hw1 : w.1 ∈ S p) (hw2 : w.2 ∈ S p)
    (horth : v.1 * w.2 - v.2 * w.1 = 0) :
    omegaL (castV p v) (castV p w) = 0 := by
  have hg := ((good_red hv1).mul (good_red hw2)).sub
    ((good_red hv2).mul (good_red hw1))
  rw [omegaL_apply]
  change rfH p (red p v.1) * rfH p (red p w.2) -
    rfH p (red p v.2) * rfH p (red p w.1) = 0
  rw [← map_mul, ← map_mul, ← map_sub, ← hg.eq, horth, (Good.zero (ℓ := p)).eq, map_zero]

/-- One nonzero reduced coordinate suffices for a nonzero load pair. -/
theorem castV_ne_zero_of_fst (v : ℚ × ℚ) (hv : red p v.1 ≠ 0) : castV p v ≠ 0 := by
  intro h
  have hf := congrArg Prod.fst h
  change rfH p (red p v.1) = 0 at hf
  exact hv (rfH_injective (by simpa only [map_zero] using hf))

theorem castV_ne_zero_of_snd (v : ℚ × ℚ) (hv : red p v.2 ≠ 0) : castV p v ≠ 0 := by
  intro h
  have hf := congrArg Prod.snd h
  change rfH p (red p v.2) = 0 at hf
  exact hv (rfH_injective (by simpa only [map_zero] using hf))

#print axioms rational_red_ne_zero
#print axioms castV_omega_eq_zero
#print axioms castV_ne_zero_of_fst
end CatalanCore.Uniform.Content.RankProducer
