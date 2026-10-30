import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C13T01
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C13T01_small_kills : C13T01.kr.card ≤ 1 ∧ C13T01.kc.card ≤ 1 := by decide +kernel

theorem C13T01_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T01.Integral p := by
  apply C13T01_integral p
  intro hd
  have hpos : 0 < C13T01_den := by decide +kernel
  have hbound : C13T01_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T01_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T01.kr, castV p (C13T01.rload d) ≠ 0) ∧
    (∀ d ∈ C13T01.kc, castV p (C13T01.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T01.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T01.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T01_cload_6]
    exact rank_castV_ne_zero_of_fst p ((395304946674811193973238466588293 / 1356623644835486562081792240411000), (-683210031796143901343965148836559 / 4069870934506459686245376721233000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T01_large_integral
#print axioms C13T01_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
