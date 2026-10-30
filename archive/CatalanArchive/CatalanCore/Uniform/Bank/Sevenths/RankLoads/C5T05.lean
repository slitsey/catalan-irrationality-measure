import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5T05
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C5T05_small_kills : C5T05.kr.card ≤ 1 ∧ C5T05.kc.card ≤ 1 := by decide +kernel

theorem C5T05_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T05.Integral p := by
  apply C5T05_integral p
  intro hd
  have hpos : 0 < C5T05_den := by decide +kernel
  have hbound : C5T05_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T05_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T05.kr, castV p (C5T05.rload d) ≠ 0) ∧
    (∀ d ∈ C5T05.kc, castV p (C5T05.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T05.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T05.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T05_cload_5]
    exact rank_castV_ne_zero_of_fst p ((65033412544380867527211715151743 / 67391433797389529022169033434080), (-3736713636642434958236829974636717 / 2089134447719075399687240036456480)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T05_large_integral
#print axioms C5T05_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
