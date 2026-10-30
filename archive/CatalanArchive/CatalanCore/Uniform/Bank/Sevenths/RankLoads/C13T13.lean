import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C13T13
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C13T13_small_kills : C13T13.kr.card ≤ 1 ∧ C13T13.kc.card ≤ 1 := by decide +kernel

theorem C13T13_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T13.Integral p := by
  apply C13T13_integral p
  intro hd
  have hpos : 0 < C13T13_den := by decide +kernel
  have hbound : C13T13_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T13_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T13.kr, castV p (C13T13.rload d) ≠ 0) ∧
    (∀ d ∈ C13T13.kc, castV p (C13T13.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T13.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T13.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T13_cload_4]
    exact rank_castV_ne_zero_of_fst p ((75744137104057904693 / 96391624834621345320), (-2655682076987821727 / 10710180537180149480)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T13_large_integral
#print axioms C13T13_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
