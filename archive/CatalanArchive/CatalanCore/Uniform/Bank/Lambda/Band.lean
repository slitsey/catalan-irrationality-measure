import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.Roots
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid

/-- The norm-one Lambda coefficients are integral at every prime. -/
theorem D4_coeff_mem (a p : ℕ) [Fact p.Prime] (i : Fin 2) : (D4 a).c i ∈ S p := by
  fin_cases i
  · change (-1 : ℚ) ∈ S p
    exact (S p).neg_mem (S p).one_mem
  · change (1 : ℚ) ∈ S p
    exact (S p).one_mem

theorem D4_den_units (a p : ℕ) [hp : Fact p.Prime] (hp4 : ¬ p ∣ 4) (i : Fin 2) :
    ¬ p ∣ (D4 a).q i := by
  fin_cases i
  · exact hp4
  · exact hp.out.not_dvd_one

theorem D4_band (a r m p : ℕ) (ha : a = 1 ∨ a = 3) (hp : 29 ≤ p)
    (hrp : r ≤ 5 * p) (hm : 10 * m ≤ r + 5) (i : Fin 2) :
    (D4 a).q i * (r + 2 * m) + (D4 a).u i ≤ p ^ 2 := by
  have h := q4_band r m p a ha hp hrp hm
  fin_cases i
  · exact h.2.1
  · exact h.2.2

/-- The actual q4 pole split, with all band and coefficient obligations discharged. -/
noncomputable def lambdaPoleSplit (a p r m : ℕ) [Fact p.Prime]
    (ha : a = 1 ∨ a = 3) (hp : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm : 10 * m ≤ r + 5) :
    PoleSplit p (r + 2 * m) (D4 a).f (D4 a).e :=
  (D4 a).poleSplit (r + 2 * m) (D4_coeff_mem a p) (D4_den_units a p hp4)
    (by omega) (D4_band a r m p ha hp hrp hm)

#print axioms D4_band
end CatalanCore.Uniform.Bank.Lambda
