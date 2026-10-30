import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C13T26
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C13T26_small_kills : C13T26.kr.card ≤ 1 ∧ C13T26.kc.card ≤ 1 := by decide +kernel

theorem C13T26_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T26.Integral p := by
  apply C13T26_integral p
  intro hd
  have hpos : 0 < C13T26_den := by decide +kernel
  have hbound : C13T26_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T26_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T26.kr, castV p (C13T26.rload d) ≠ 0) ∧
    (∀ d ∈ C13T26.kc, castV p (C13T26.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T26.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T26_rload_2]
    exact rank_castV_ne_zero_of_fst p ((-46 / 39), (-4 / 39)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T26.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T26_large_integral
#print axioms C13T26_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
