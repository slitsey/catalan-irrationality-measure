import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T04
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T04_small_kills : C1T04.kr.card ≤ 1 ∧ C1T04.kc.card ≤ 1 := by decide +kernel

theorem C1T04_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T04.Integral p := by
  apply C1T04_integral p
  intro hd
  have hpos : 0 < C1T04_den := by decide +kernel
  have hbound : C1T04_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T04_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T04.kr, castV p (C1T04.rload d) ≠ 0) ∧
    (∀ d ∈ C1T04.kc, castV p (C1T04.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T04.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T04.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T04_large_integral
#print axioms C1T04_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
