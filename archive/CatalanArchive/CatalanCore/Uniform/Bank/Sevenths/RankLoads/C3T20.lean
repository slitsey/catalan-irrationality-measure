import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3T20
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T20_small_kills : C3T20.kr.card ≤ 1 ∧ C3T20.kc.card ≤ 1 := by decide +kernel

theorem C3T20_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T20.Integral p := by
  apply C3T20_integral p
  intro hd
  have hpos : 0 < C3T20_den := by decide +kernel
  have hbound : C3T20_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T20_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T20.kr, castV p (C3T20.rload d) ≠ 0) ∧
    (∀ d ∈ C3T20.kc, castV p (C3T20.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T20.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T20.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T20_cload_3]
    exact rank_castV_ne_zero_of_fst p ((-74006459 / 197174400), (-29514697 / 98587200)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T20_large_integral
#print axioms C3T20_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
