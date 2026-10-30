import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3T35
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T35_small_kills : C3T35.kr.card ≤ 1 ∧ C3T35.kc.card ≤ 1 := by decide +kernel

theorem C3T35_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T35.Integral p := by
  apply C3T35_integral p
  intro hd
  have hpos : 0 < C3T35_den := by decide +kernel
  have hbound : C3T35_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T35_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T35.kr, castV p (C3T35.rload d) ≠ 0) ∧
    (∀ d ∈ C3T35.kc, castV p (C3T35.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T35.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T35_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T35.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T35_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T35_large_integral
#print axioms C3T35_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
