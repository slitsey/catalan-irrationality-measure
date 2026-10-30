import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T00
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T00_small_kills : C1T00.kr.card ≤ 1 ∧ C1T00.kc.card ≤ 1 := by decide +kernel

theorem C1T00_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T00.Integral p := by
  apply C1T00_integral p
  intro hd
  have hpos : 0 < C1T00_den := by decide +kernel
  have hbound : C1T00_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T00_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T00.kr, castV p (C1T00.rload d) ≠ 0) ∧
    (∀ d ∈ C1T00.kc, castV p (C1T00.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T00.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T00.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T00_cload_5]
    exact rank_castV_ne_zero_of_fst p ((-23019541031259901542239981 / 177642557209210434046755075), (-88115843712078784229233687 / 36439498914709832624975400)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T00_large_integral
#print axioms C1T00_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
