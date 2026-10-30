import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T16
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T16_small_kills : C1T16.kr.card ≤ 1 ∧ C1T16.kc.card ≤ 1 := by decide +kernel

theorem C1T16_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T16.Integral p := by
  apply C1T16_integral p
  intro hd
  have hpos : 0 < C1T16_den := by decide +kernel
  have hbound : C1T16_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T16_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T16.kr, castV p (C1T16.rload d) ≠ 0) ∧
    (∀ d ∈ C1T16.kc, castV p (C1T16.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T16.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T16_rload_3]
    exact rank_castV_ne_zero_of_fst p ((-1397921 / 1458540), (-2931619 / 1458540)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T16.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T16_large_integral
#print axioms C1T16_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
