import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3T26
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T26_small_kills : C3T26.kr.card ≤ 1 ∧ C3T26.kc.card ≤ 1 := by decide +kernel

theorem C3T26_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T26.Integral p := by
  apply C3T26_integral p
  intro hd
  have hpos : 0 < C3T26_den := by decide +kernel
  have hbound : C3T26_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T26_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T26.kr, castV p (C3T26.rload d) ≠ 0) ∧
    (∀ d ∈ C3T26.kc, castV p (C3T26.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T26.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T26_rload_2]
    exact rank_castV_ne_zero_of_fst p ((-101 / 80), (-29 / 120)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T26.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T26_large_integral
#print axioms C3T26_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
