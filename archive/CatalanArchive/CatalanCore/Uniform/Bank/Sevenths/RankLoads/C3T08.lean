import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3T08
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T08_small_kills : C3T08.kr.card ≤ 1 ∧ C3T08.kc.card ≤ 1 := by decide +kernel

theorem C3T08_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T08.Integral p := by
  apply C3T08_integral p
  intro hd
  have hpos : 0 < C3T08_den := by decide +kernel
  have hbound : C3T08_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T08_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T08.kr, castV p (C3T08.rload d) ≠ 0) ∧
    (∀ d ∈ C3T08.kc, castV p (C3T08.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T08.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T08.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T08_cload_5]
    exact rank_castV_ne_zero_of_fst p ((193131983321318700128386 / 1236718077708539662968875), (-1402631172187181546136 / 3805286392949352809135)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T08_large_integral
#print axioms C3T08_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
