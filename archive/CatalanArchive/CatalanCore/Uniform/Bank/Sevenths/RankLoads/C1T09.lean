import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T09
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T09_small_kills : C1T09.kr.card ≤ 1 ∧ C1T09.kc.card ≤ 1 := by decide +kernel

theorem C1T09_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T09.Integral p := by
  apply C1T09_integral p
  intro hd
  have hpos : 0 < C1T09_den := by decide +kernel
  have hbound : C1T09_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T09_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T09.kr, castV p (C1T09.rload d) ≠ 0) ∧
    (∀ d ∈ C1T09.kc, castV p (C1T09.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T09.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T09_rload_5]
    exact rank_castV_ne_zero_of_fst p ((-620872194061560215917994033 / 1183934788022501064083853000), (-3638866639296810540691286813 / 789289858681667376055902000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T09.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T09_large_integral
#print axioms C1T09_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
