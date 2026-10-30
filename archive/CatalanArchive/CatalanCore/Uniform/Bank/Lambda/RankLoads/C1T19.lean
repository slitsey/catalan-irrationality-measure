import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T19
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T19_small_kills : C1T19.kr.card ≤ 1 ∧ C1T19.kc.card ≤ 1 := by decide +kernel

theorem C1T19_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T19.Integral p := by
  apply C1T19_integral p
  intro hd
  have hpos : 0 < C1T19_den := by decide +kernel
  have hbound : C1T19_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T19_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T19.kr, castV p (C1T19.rload d) ≠ 0) ∧
    (∀ d ∈ C1T19.kc, castV p (C1T19.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T19.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T19.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T19_large_integral
#print axioms C1T19_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
