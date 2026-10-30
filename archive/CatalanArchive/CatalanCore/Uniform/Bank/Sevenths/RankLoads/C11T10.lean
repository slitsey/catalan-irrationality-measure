import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C11T10
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C11T10_small_kills : C11T10.kr.card ≤ 1 ∧ C11T10.kc.card ≤ 1 := by decide +kernel

theorem C11T10_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T10.Integral p := by
  apply C11T10_integral p
  intro hd
  have hpos : 0 < C11T10_den := by decide +kernel
  have hbound : C11T10_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T10_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T10.kr, castV p (C11T10.rload d) ≠ 0) ∧
    (∀ d ∈ C11T10.kc, castV p (C11T10.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T10.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T10.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T10_large_integral
#print axioms C11T10_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
