import CatalanCore.Uniform.Bank.Lambda.RankPalette.C3T26
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T26_small_kills : C3T26.kr.card ≤ 1 ∧ C3T26.kc.card ≤ 1 := by decide +kernel

theorem C3T26_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T26.Integral p := by
  apply C3T26_integral p
  intro hd
  have hpos : 0 < C3T26_den := by decide +kernel
  have hbound : C3T26_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T26_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T26.kr, castV p (C3T26.rload d) ≠ 0) ∧
    (∀ d ∈ C3T26.kc, castV p (C3T26.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T26.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T26.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T26_cload_1]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T26_large_integral
#print axioms C3T26_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
