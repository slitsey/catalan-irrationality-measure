import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C11T23
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C11T23_small_kills : C11T23.kr.card ≤ 1 ∧ C11T23.kc.card ≤ 1 := by decide +kernel

theorem C11T23_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T23.Integral p := by
  apply C11T23_integral p
  intro hd
  have hpos : 0 < C11T23_den := by decide +kernel
  have hbound : C11T23_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T23_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T23.kr, castV p (C11T23.rload d) ≠ 0) ∧
    (∀ d ∈ C11T23.kc, castV p (C11T23.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T23.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T23_rload_2]
    exact rank_castV_ne_zero_of_fst p ((2664353 / 2709288), (-950765 / 301032)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T23.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T23_large_integral
#print axioms C11T23_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
