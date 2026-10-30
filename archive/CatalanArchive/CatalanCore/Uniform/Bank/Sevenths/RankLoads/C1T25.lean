import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T25
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T25_small_kills : C1T25.kr.card ≤ 1 ∧ C1T25.kc.card ≤ 1 := by decide +kernel

theorem C1T25_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T25.Integral p := by
  apply C1T25_integral p
  intro hd
  have hpos : 0 < C1T25_den := by decide +kernel
  have hbound : C1T25_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T25_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T25.kr, castV p (C1T25.rload d) ≠ 0) ∧
    (∀ d ∈ C1T25.kc, castV p (C1T25.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T25.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T25.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T25_large_integral
#print axioms C1T25_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
