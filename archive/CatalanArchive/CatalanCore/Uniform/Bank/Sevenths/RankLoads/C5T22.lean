import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5T22
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C5T22_small_kills : C5T22.kr.card ≤ 1 ∧ C5T22.kc.card ≤ 1 := by decide +kernel

theorem C5T22_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T22.Integral p := by
  apply C5T22_integral p
  intro hd
  have hpos : 0 < C5T22_den := by decide +kernel
  have hbound : C5T22_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T22_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T22.kr, castV p (C5T22.rload d) ≠ 0) ∧
    (∀ d ∈ C5T22.kc, castV p (C5T22.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T22.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T22.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T22_large_integral
#print axioms C5T22_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
