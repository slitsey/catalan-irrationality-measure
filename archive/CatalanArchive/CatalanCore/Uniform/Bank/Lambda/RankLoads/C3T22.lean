import CatalanCore.Uniform.Bank.Lambda.RankPalette.C3T22
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T22_small_kills : C3T22.kr.card ≤ 1 ∧ C3T22.kc.card ≤ 1 := by decide +kernel

theorem C3T22_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T22.Integral p := by
  apply C3T22_integral p
  intro hd
  have hpos : 0 < C3T22_den := by decide +kernel
  have hbound : C3T22_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T22_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T22.kr, castV p (C3T22.rload d) ≠ 0) ∧
    (∀ d ∈ C3T22.kc, castV p (C3T22.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T22.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T22.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T22_large_integral
#print axioms C3T22_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
