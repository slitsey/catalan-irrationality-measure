import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5T32
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C5T32_small_kills : C5T32.kr.card ≤ 1 ∧ C5T32.kc.card ≤ 1 := by decide +kernel

theorem C5T32_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T32.Integral p := by
  apply C5T32_integral p
  intro hd
  have hpos : 0 < C5T32_den := by decide +kernel
  have hbound : C5T32_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T32_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T32.kr, castV p (C5T32.rload d) ≠ 0) ∧
    (∀ d ∈ C5T32.kc, castV p (C5T32.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T32.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T32.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T32_large_integral
#print axioms C5T32_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
