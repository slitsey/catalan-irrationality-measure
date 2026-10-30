import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C13T32
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C13T32_small_kills : C13T32.kr.card ≤ 1 ∧ C13T32.kc.card ≤ 1 := by decide +kernel

theorem C13T32_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T32.Integral p := by
  apply C13T32_integral p
  intro hd
  have hpos : 0 < C13T32_den := by decide +kernel
  have hbound : C13T32_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T32_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T32.kr, castV p (C13T32.rload d) ≠ 0) ∧
    (∀ d ∈ C13T32.kc, castV p (C13T32.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T32.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T32.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T32_cload_1]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T32_large_integral
#print axioms C13T32_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
