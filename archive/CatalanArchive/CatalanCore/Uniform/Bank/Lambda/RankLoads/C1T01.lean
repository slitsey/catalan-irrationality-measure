import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T01
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T01_small_kills : C1T01.kr.card ≤ 1 ∧ C1T01.kc.card ≤ 1 := by decide +kernel

theorem C1T01_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T01.Integral p := by
  apply C1T01_integral p
  intro hd
  have hpos : 0 < C1T01_den := by decide +kernel
  have hbound : C1T01_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T01_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T01.kr, castV p (C1T01.rload d) ≠ 0) ∧
    (∀ d ∈ C1T01.kc, castV p (C1T01.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T01.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T01_rload_5]
    exact rank_castV_ne_zero_of_fst p ((-23019541031259901542239981 / 177642557209210434046755075), (-88115843712078784229233687 / 36439498914709832624975400)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T01.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T01_large_integral
#print axioms C1T01_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
