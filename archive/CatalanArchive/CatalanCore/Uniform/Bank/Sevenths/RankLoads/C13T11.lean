import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C13T11
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C13T11_small_kills : C13T11.kr.card ≤ 1 ∧ C13T11.kc.card ≤ 1 := by decide +kernel

theorem C13T11_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T11.Integral p := by
  apply C13T11_integral p
  intro hd
  have hpos : 0 < C13T11_den := by decide +kernel
  have hbound : C13T11_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T11_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T11.kr, castV p (C13T11.rload d) ≠ 0) ∧
    (∀ d ∈ C13T11.kc, castV p (C13T11.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T11.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T11.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T11_large_integral
#print axioms C13T11_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
