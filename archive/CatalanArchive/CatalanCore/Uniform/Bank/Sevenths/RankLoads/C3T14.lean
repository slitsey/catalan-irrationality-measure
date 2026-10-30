import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3T14
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T14_small_kills : C3T14.kr.card ≤ 1 ∧ C3T14.kc.card ≤ 1 := by decide +kernel

theorem C3T14_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T14.Integral p := by
  apply C3T14_integral p
  intro hd
  have hpos : 0 < C3T14_den := by decide +kernel
  have hbound : C3T14_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T14_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T14.kr, castV p (C3T14.rload d) ≠ 0) ∧
    (∀ d ∈ C3T14.kc, castV p (C3T14.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T14.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T14_rload_4]
    exact rank_castV_ne_zero_of_fst p ((-71134325929822 / 2082470422341855), (-141287501650532 / 416494084468371)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T14.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T14_large_integral
#print axioms C3T14_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
