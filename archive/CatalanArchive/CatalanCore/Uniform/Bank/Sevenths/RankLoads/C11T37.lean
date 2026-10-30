import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C11T37
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C11T37_small_kills : C11T37.kr.card ≤ 1 ∧ C11T37.kc.card ≤ 1 := by decide +kernel

theorem C11T37_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T37.Integral p := by
  apply C11T37_integral p
  intro hd
  have hpos : 0 < C11T37_den := by decide +kernel
  have hbound : C11T37_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T37_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T37.kr, castV p (C11T37.rload d) ≠ 0) ∧
    (∀ d ∈ C11T37.kc, castV p (C11T37.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T37.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T37.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T37_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (-7 / 2)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T37_large_integral
#print axioms C11T37_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
