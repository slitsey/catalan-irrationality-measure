import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C11T30
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C11T30_small_kills : C11T30.kr.card ≤ 1 ∧ C11T30.kc.card ≤ 1 := by decide +kernel

theorem C11T30_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T30.Integral p := by
  apply C11T30_integral p
  intro hd
  have hpos : 0 < C11T30_den := by decide +kernel
  have hbound : C11T30_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T30_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T30.kr, castV p (C11T30.rload d) ≠ 0) ∧
    (∀ d ∈ C11T30.kc, castV p (C11T30.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T30.kr = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T30_rload_1]
    exact rank_castV_ne_zero_of_fst p ((433 / 441), (-45 / 14)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T30.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T30_large_integral
#print axioms C11T30_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
