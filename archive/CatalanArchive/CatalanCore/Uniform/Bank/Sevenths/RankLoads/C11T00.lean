import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C11T00
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C11T00_small_kills : C11T00.kr.card ≤ 1 ∧ C11T00.kc.card ≤ 1 := by decide +kernel

theorem C11T00_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T00.Integral p := by
  apply C11T00_integral p
  intro hd
  have hpos : 0 < C11T00_den := by decide +kernel
  have hbound : C11T00_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T00_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T00.kr, castV p (C11T00.rload d) ≠ 0) ∧
    (∀ d ∈ C11T00.kc, castV p (C11T00.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T00.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T00_rload_6]
    exact rank_castV_ne_zero_of_fst p ((1730829760278160905139789902184333487 / 16343077720378337911866161413462200000), (-10560437972615517451291007915544105583 / 4902923316113501373559848424038660000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T00.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T00_large_integral
#print axioms C11T00_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
