import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3T34
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T34_small_kills : C3T34.kr.card ≤ 1 ∧ C3T34.kc.card ≤ 1 := by decide +kernel

theorem C3T34_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T34.Integral p := by
  apply C3T34_integral p
  intro hd
  have hpos : 0 < C3T34_den := by decide +kernel
  have hbound : C3T34_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T34_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T34.kr, castV p (C3T34.rload d) ≠ 0) ∧
    (∀ d ∈ C3T34.kc, castV p (C3T34.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T34.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T34.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T34_large_integral
#print axioms C3T34_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
