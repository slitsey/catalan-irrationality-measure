import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C13T05
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C13T05_small_kills : C13T05.kr.card ≤ 1 ∧ C13T05.kc.card ≤ 1 := by decide +kernel

theorem C13T05_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T05.Integral p := by
  apply C13T05_integral p
  intro hd
  have hpos : 0 < C13T05_den := by decide +kernel
  have hbound : C13T05_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T05_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T05.kr, castV p (C13T05.rload d) ≠ 0) ∧
    (∀ d ∈ C13T05.kc, castV p (C13T05.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T05.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T05.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T05_cload_5]
    exact rank_castV_ne_zero_of_fst p ((43799018387332640851662856305721 / 54128017442428290423669966021000), (-4446727150550975595458036743817 / 18042672480809430141223322007000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T05_large_integral
#print axioms C13T05_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
