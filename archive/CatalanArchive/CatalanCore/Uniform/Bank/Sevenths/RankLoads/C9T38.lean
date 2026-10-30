import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C9T38
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C9T38_small_kills : C9T38.kr.card ≤ 1 ∧ C9T38.kc.card ≤ 1 := by decide +kernel

theorem C9T38_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T38.Integral p := by
  apply C9T38_integral p
  intro hd
  have hpos : 0 < C9T38_den := by decide +kernel
  have hbound : C9T38_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T38_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T38.kr, castV p (C9T38.rload d) ≠ 0) ∧
    (∀ d ∈ C9T38.kc, castV p (C9T38.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T38.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T38_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T38.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T38_large_integral
#print axioms C9T38_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
