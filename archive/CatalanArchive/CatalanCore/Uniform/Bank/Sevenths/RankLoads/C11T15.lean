import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C11T15
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C11T15_small_kills : C11T15.kr.card ≤ 1 ∧ C11T15.kc.card ≤ 1 := by decide +kernel

theorem C11T15_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T15.Integral p := by
  apply C11T15_integral p
  intro hd
  have hpos : 0 < C11T15_den := by decide +kernel
  have hbound : C11T15_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T15_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T15.kr, castV p (C11T15.rload d) ≠ 0) ∧
    (∀ d ∈ C11T15.kc, castV p (C11T15.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T15.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T15.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T15_cload_4]
    exact rank_castV_ne_zero_of_fst p ((-408997458901 / 1209399735600), (-918039340807 / 483759894240)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T15_large_integral
#print axioms C11T15_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
