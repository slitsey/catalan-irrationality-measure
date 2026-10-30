import CatalanCore.Uniform.Bank.Sevenths.PolePalette
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid

theorem D7Frame_coeff_mem (a p : ℕ) [Fact p.Prime] (i : Fin 2) : (D7Frame a).c i ∈ S p := by
  fin_cases i
  · change (-1 : ℚ) ∈ S p
    exact (S p).neg_mem (S p).one_mem
  · change (1 : ℚ) ∈ S p
    exact (S p).one_mem

theorem D7Frame_den_units (a p : ℕ) [hp : Fact p.Prime] (hp7 : ¬ p ∣ 7) (i : Fin 2) :
    ¬ p ∣ (D7Frame a).q i := by
  fin_cases i
  · exact hp7
  · exact hp.out.not_dvd_one

theorem D7Frame_band (a r m p : ℕ) (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p)
    (hrp : r ≤ 6 * p) (hm : 12 * m ≤ r + 6) (i : Fin 2) :
    (D7Frame a).q i * (r + 2 * m) + (D7Frame a).u i ≤ p ^ 2 := by
  have hN : r + 2 * m ≤ 7 * p + 1 := by omega
  have hpp : 64 * p ≤ p ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_right p hp64
  fin_cases i
  · change 7 * (r + 2 * m) + a ≤ p ^ 2
    nlinarith [ha.2]
  · change 1 * (r + 2 * m) + 1 ≤ p ^ 2
    nlinarith

noncomputable def seventhsPoleSplit (a p r m : ℕ) [Fact p.Prime]
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm : 12 * m ≤ r + 6) :
    PoleSplit p (r + 2 * m) (D7Frame a).f (D7Frame a).e :=
  (D7Frame a).poleSplit (r + 2 * m) (D7Frame_coeff_mem a p) (D7Frame_den_units a p hp7)
    (by omega) (D7Frame_band a r m p ha hp64 hrp hm)

#print axioms D7Frame_band
end CatalanCore.Uniform.Bank.Sevenths
