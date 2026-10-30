import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C13T28
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C13T28_small_kills : C13T28.kr.card ≤ 1 ∧ C13T28.kc.card ≤ 1 := by decide +kernel

theorem C13T28_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T28.Integral p := by
  apply C13T28_integral p
  intro hd
  have hpos : 0 < C13T28_den := by decide +kernel
  have hbound : C13T28_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T28_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T28.kr, castV p (C13T28.rload d) ≠ 0) ∧
    (∀ d ∈ C13T28.kc, castV p (C13T28.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T28.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T28.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T28_large_integral
#print axioms C13T28_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
