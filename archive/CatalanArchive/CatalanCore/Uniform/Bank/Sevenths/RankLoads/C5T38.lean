import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5T38
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C5T38_small_kills : C5T38.kr.card ≤ 1 ∧ C5T38.kc.card ≤ 1 := by decide +kernel

theorem C5T38_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T38.Integral p := by
  apply C5T38_integral p
  intro hd
  have hpos : 0 < C5T38_den := by decide +kernel
  have hbound : C5T38_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T38_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T38.kr, castV p (C5T38.rload d) ≠ 0) ∧
    (∀ d ∈ C5T38.kc, castV p (C5T38.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T38.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T38_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T38.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T38_large_integral
#print axioms C5T38_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
