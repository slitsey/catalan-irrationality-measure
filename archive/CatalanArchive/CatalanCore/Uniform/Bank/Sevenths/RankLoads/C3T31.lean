import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3T31
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T31_small_kills : C3T31.kr.card ≤ 1 ∧ C3T31.kc.card ≤ 1 := by decide +kernel

theorem C3T31_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T31.Integral p := by
  apply C3T31_integral p
  intro hd
  have hpos : 0 < C3T31_den := by decide +kernel
  have hbound : C3T31_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T31_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T31.kr, castV p (C3T31.rload d) ≠ 0) ∧
    (∀ d ∈ C3T31.kc, castV p (C3T31.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T31.kr = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T31_rload_1]
    exact rank_castV_ne_zero_of_fst p ((463 / 588), (-24 / 35)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T31.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T31_large_integral
#print axioms C3T31_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
