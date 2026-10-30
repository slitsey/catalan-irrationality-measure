import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T22
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T22_small_kills : C1T22.kr.card ≤ 1 ∧ C1T22.kc.card ≤ 1 := by decide +kernel

theorem C1T22_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T22.Integral p := by
  apply C1T22_integral p
  intro hd
  have hpos : 0 < C1T22_den := by decide +kernel
  have hbound : C1T22_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T22_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T22.kr, castV p (C1T22.rload d) ≠ 0) ∧
    (∀ d ∈ C1T22.kc, castV p (C1T22.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T22.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T22.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T22_cload_2]
    exact rank_castV_ne_zero_of_fst p ((-12 / 5), (-33 / 20)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T22_large_integral
#print axioms C1T22_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
