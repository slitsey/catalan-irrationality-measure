import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T06
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T06_small_kills : C1T06.kr.card ≤ 1 ∧ C1T06.kc.card ≤ 1 := by decide +kernel

theorem C1T06_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T06.Integral p := by
  apply C1T06_integral p
  intro hd
  have hpos : 0 < C1T06_den := by decide +kernel
  have hbound : C1T06_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T06_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T06.kr, castV p (C1T06.rload d) ≠ 0) ∧
    (∀ d ∈ C1T06.kc, castV p (C1T06.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T06.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T06_rload_5]
    exact rank_castV_ne_zero_of_fst p ((161095237687746216896798069934142109 / 161343721758715873364292979985985795), (-14632101432614264961069085104418237891 / 2151249623449544978190573066479810600)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T06.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T06_large_integral
#print axioms C1T06_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
