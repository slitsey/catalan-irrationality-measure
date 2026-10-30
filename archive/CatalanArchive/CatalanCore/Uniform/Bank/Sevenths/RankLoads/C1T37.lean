import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T37
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T37_small_kills : C1T37.kr.card ≤ 1 ∧ C1T37.kc.card ≤ 1 := by decide +kernel

theorem C1T37_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T37.Integral p := by
  apply C1T37_integral p
  intro hd
  have hpos : 0 < C1T37_den := by decide +kernel
  have hbound : C1T37_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T37_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T37.kr, castV p (C1T37.rload d) ≠ 0) ∧
    (∀ d ∈ C1T37.kc, castV p (C1T37.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T37.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T37_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T37.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T37_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T37_large_integral
#print axioms C1T37_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
