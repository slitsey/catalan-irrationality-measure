import CatalanCore.Uniform.Bank.Lambda.RankPalette.C3T10
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T10_small_kills : C3T10.kr.card ≤ 1 ∧ C3T10.kc.card ≤ 1 := by decide +kernel

theorem C3T10_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T10.Integral p := by
  apply C3T10_integral p
  intro hd
  have hpos : 0 < C3T10_den := by decide +kernel
  have hbound : C3T10_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T10_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T10.kr, castV p (C3T10.rload d) ≠ 0) ∧
    (∀ d ∈ C3T10.kc, castV p (C3T10.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T10.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T10.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T10_large_integral
#print axioms C3T10_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
