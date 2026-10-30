import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C13T06
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C13T06_small_kills : C13T06.kr.card ≤ 1 ∧ C13T06.kc.card ≤ 1 := by decide +kernel

theorem C13T06_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T06.Integral p := by
  apply C13T06_integral p
  intro hd
  have hpos : 0 < C13T06_den := by decide +kernel
  have hbound : C13T06_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T06_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T06.kr, castV p (C13T06.rload d) ≠ 0) ∧
    (∀ d ∈ C13T06.kc, castV p (C13T06.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T06.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T06_rload_5]
    exact rank_castV_ne_zero_of_fst p ((43799018387332640851662856305721 / 54128017442428290423669966021000), (-4446727150550975595458036743817 / 18042672480809430141223322007000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T06.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T06_large_integral
#print axioms C13T06_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
