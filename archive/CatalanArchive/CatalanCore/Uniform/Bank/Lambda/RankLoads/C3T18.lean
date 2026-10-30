import CatalanCore.Uniform.Bank.Lambda.RankPalette.C3T18
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T18_small_kills : C3T18.kr.card ≤ 1 ∧ C3T18.kc.card ≤ 1 := by decide +kernel

theorem C3T18_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T18.Integral p := by
  apply C3T18_integral p
  intro hd
  have hpos : 0 < C3T18_den := by decide +kernel
  have hbound : C3T18_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T18_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T18.kr, castV p (C3T18.rload d) ≠ 0) ∧
    (∀ d ∈ C3T18.kc, castV p (C3T18.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T18.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T18_rload_2]
    exact rank_castV_ne_zero_of_fst p ((429290 / 543851), (-481787 / 932316)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T18.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T18_large_integral
#print axioms C3T18_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
