import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T23
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T23_small_kills : C1T23.kr.card ≤ 1 ∧ C1T23.kc.card ≤ 1 := by decide +kernel

theorem C1T23_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T23.Integral p := by
  apply C1T23_integral p
  intro hd
  have hpos : 0 < C1T23_den := by decide +kernel
  have hbound : C1T23_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T23_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T23.kr, castV p (C1T23.rload d) ≠ 0) ∧
    (∀ d ∈ C1T23.kc, castV p (C1T23.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T23.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T23_rload_2]
    exact rank_castV_ne_zero_of_fst p ((12206183 / 12234240), (-869867 / 127440)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T23.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T23_large_integral
#print axioms C1T23_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
