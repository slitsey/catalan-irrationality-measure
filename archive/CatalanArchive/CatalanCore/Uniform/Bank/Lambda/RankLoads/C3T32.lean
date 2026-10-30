import CatalanCore.Uniform.Bank.Lambda.RankPalette.C3T32
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T32_small_kills : C3T32.kr.card ≤ 1 ∧ C3T32.kc.card ≤ 1 := by decide +kernel

theorem C3T32_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T32.Integral p := by
  apply C3T32_integral p
  intro hd
  have hpos : 0 < C3T32_den := by decide +kernel
  have hbound : C3T32_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T32_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T32.kr, castV p (C3T32.rload d) ≠ 0) ∧
    (∀ d ∈ C3T32.kc, castV p (C3T32.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T32.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T32_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T32.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T32_large_integral
#print axioms C3T32_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
