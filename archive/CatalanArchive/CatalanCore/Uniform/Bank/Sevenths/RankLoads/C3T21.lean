import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3T21
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T21_small_kills : C3T21.kr.card ≤ 1 ∧ C3T21.kc.card ≤ 1 := by decide +kernel

theorem C3T21_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T21.Integral p := by
  apply C3T21_integral p
  intro hd
  have hpos : 0 < C3T21_den := by decide +kernel
  have hbound : C3T21_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T21_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T21.kr, castV p (C3T21.rload d) ≠ 0) ∧
    (∀ d ∈ C3T21.kc, castV p (C3T21.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T21.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T21_rload_3]
    exact rank_castV_ne_zero_of_fst p ((-74006459 / 197174400), (-29514697 / 98587200)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T21.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T21_large_integral
#print axioms C3T21_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
