import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C11T36
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C11T36_small_kills : C11T36.kr.card ≤ 1 ∧ C11T36.kc.card ≤ 1 := by decide +kernel

theorem C11T36_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T36.Integral p := by
  apply C11T36_integral p
  intro hd
  have hpos : 0 < C11T36_den := by decide +kernel
  have hbound : C11T36_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T36_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T36.kr, castV p (C11T36.rload d) ≠ 0) ∧
    (∀ d ∈ C11T36.kc, castV p (C11T36.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T36.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T36_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (-7 / 2)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T36.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T36_large_integral
#print axioms C11T36_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
