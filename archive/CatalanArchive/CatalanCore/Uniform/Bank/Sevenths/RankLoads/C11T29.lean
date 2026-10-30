import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C11T29
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C11T29_small_kills : C11T29.kr.card ≤ 1 ∧ C11T29.kc.card ≤ 1 := by decide +kernel

theorem C11T29_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T29.Integral p := by
  apply C11T29_integral p
  intro hd
  have hpos : 0 < C11T29_den := by decide +kernel
  have hbound : C11T29_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T29_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T29.kr, castV p (C11T29.rload d) ≠ 0) ∧
    (∀ d ∈ C11T29.kc, castV p (C11T29.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T29.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T29.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T29_cload_1]
    exact rank_castV_ne_zero_of_fst p ((433 / 441), (-45 / 14)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T29_large_integral
#print axioms C11T29_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
