import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3T09
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T09_small_kills : C3T09.kr.card ≤ 1 ∧ C3T09.kc.card ≤ 1 := by decide +kernel

theorem C3T09_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T09.Integral p := by
  apply C3T09_integral p
  intro hd
  have hpos : 0 < C3T09_den := by decide +kernel
  have hbound : C3T09_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T09_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T09.kr, castV p (C3T09.rload d) ≠ 0) ∧
    (∀ d ∈ C3T09.kc, castV p (C3T09.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T09.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T09_rload_5]
    exact rank_castV_ne_zero_of_fst p ((193131983321318700128386 / 1236718077708539662968875), (-1402631172187181546136 / 3805286392949352809135)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T09.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T09_large_integral
#print axioms C3T09_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
