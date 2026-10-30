import CatalanCore.Uniform.Bank.Lambda.RankPalette.C3T06
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T06_small_kills : C3T06.kr.card ≤ 1 ∧ C3T06.kc.card ≤ 1 := by decide +kernel

theorem C3T06_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T06.Integral p := by
  apply C3T06_integral p
  intro hd
  have hpos : 0 < C3T06_den := by decide +kernel
  have hbound : C3T06_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T06_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T06.kr, castV p (C3T06.rload d) ≠ 0) ∧
    (∀ d ∈ C3T06.kc, castV p (C3T06.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T06.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T06.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T06_cload_4]
    exact rank_castV_ne_zero_of_fst p ((75604259621642373344 / 89994173950490079655), (-6423714826532779939 / 13090061665525829768)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T06_large_integral
#print axioms C3T06_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
