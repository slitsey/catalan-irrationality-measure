import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C11T20
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C11T20_small_kills : C11T20.kr.card ≤ 1 ∧ C11T20.kc.card ≤ 1 := by decide +kernel

theorem C11T20_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T20.Integral p := by
  apply C11T20_integral p
  intro hd
  have hpos : 0 < C11T20_den := by decide +kernel
  have hbound : C11T20_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T20_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T20.kr, castV p (C11T20.rload d) ≠ 0) ∧
    (∀ d ∈ C11T20.kc, castV p (C11T20.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T20.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T20.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T20_large_integral
#print axioms C11T20_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
