import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T05
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T05_small_kills : C1T05.kr.card ≤ 1 ∧ C1T05.kc.card ≤ 1 := by decide +kernel

theorem C1T05_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T05.Integral p := by
  apply C1T05_integral p
  intro hd
  have hpos : 0 < C1T05_den := by decide +kernel
  have hbound : C1T05_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T05_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T05.kr, castV p (C1T05.rload d) ≠ 0) ∧
    (∀ d ∈ C1T05.kc, castV p (C1T05.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T05.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T05.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T05_cload_5]
    exact rank_castV_ne_zero_of_fst p ((161095237687746216896798069934142109 / 161343721758715873364292979985985795), (-14632101432614264961069085104418237891 / 2151249623449544978190573066479810600)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T05_large_integral
#print axioms C1T05_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
