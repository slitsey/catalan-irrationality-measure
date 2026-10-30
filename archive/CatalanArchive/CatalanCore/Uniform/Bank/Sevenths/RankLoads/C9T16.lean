import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C9T16
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C9T16_small_kills : C9T16.kr.card ≤ 1 ∧ C9T16.kc.card ≤ 1 := by decide +kernel

theorem C9T16_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T16.Integral p := by
  apply C9T16_integral p
  intro hd
  have hpos : 0 < C9T16_den := by decide +kernel
  have hbound : C9T16_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T16_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T16.kr, castV p (C9T16.rload d) ≠ 0) ∧
    (∀ d ∈ C9T16.kc, castV p (C9T16.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T16.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T16.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T16_large_integral
#print axioms C9T16_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
