import CatalanCore.Uniform.Bank.Lambda.RankPalette.C3T16
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T16_small_kills : C3T16.kr.card ≤ 1 ∧ C3T16.kc.card ≤ 1 := by decide +kernel

theorem C3T16_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T16.Integral p := by
  apply C3T16_integral p
  intro hd
  have hpos : 0 < C3T16_den := by decide +kernel
  have hbound : C3T16_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T16_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T16.kr, castV p (C3T16.rload d) ≠ 0) ∧
    (∀ d ∈ C3T16.kc, castV p (C3T16.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T16.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T16.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T16_large_integral
#print axioms C3T16_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
