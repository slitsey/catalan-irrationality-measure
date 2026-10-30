import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5T06
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C5T06_small_kills : C5T06.kr.card ≤ 1 ∧ C5T06.kc.card ≤ 1 := by decide +kernel

theorem C5T06_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T06.Integral p := by
  apply C5T06_integral p
  intro hd
  have hpos : 0 < C5T06_den := by decide +kernel
  have hbound : C5T06_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T06_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T06.kr, castV p (C5T06.rload d) ≠ 0) ∧
    (∀ d ∈ C5T06.kc, castV p (C5T06.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T06.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T06_rload_5]
    exact rank_castV_ne_zero_of_fst p ((65033412544380867527211715151743 / 67391433797389529022169033434080), (-3736713636642434958236829974636717 / 2089134447719075399687240036456480)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T06.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T06_large_integral
#print axioms C5T06_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
