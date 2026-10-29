module
public import CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Unique146
@[expose] public section
set_option Elab.async false

/-!
# Units modulo large primes: `D ∣ 30030^40`, `13 < p` implies `D ≠ 0` in `ZMod p`
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts6
variable {p : ℕ} [Fact p.Prime]

theorem not_dvd_30030 (hp : 13 < p) : ¬ p ∣ 30030 := by
  intro h
  have hpn := (Fact.out : p.Prime)
  have e : (30030 : ℕ) = 2 * 3 * 5 * 7 * 11 * 13 := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hpn).mp h with h | h
          · have := Nat.le_of_dvd (by norm_num) h; omega
          · have := Nat.le_of_dvd (by norm_num) h; omega
        · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  · have := Nat.le_of_dvd (by norm_num) h; omega

theorem unit_of_dvd13 (D : ℤ) (hD : D ∣ 30030 ^ 40) (hp : 13 < p) : ((D : ℤ) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have h1 : (p : ℤ) ∣ 30030 ^ 40 := h.trans hD
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have h2 : (p : ℤ) ∣ 30030 := hpp.dvd_of_dvd_pow h1
  have h3 : p ∣ 30030 := by exact_mod_cast h2
  exact not_dvd_30030 hp h3


end CatalanMeasure.GenD.Uniform.W.Charts6
