import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T22
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
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
    have he : C1T22.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T22_rload_3]
    exact rank_castV_ne_zero_of_fst p ((-25769 / 14976), (-1185469 / 307008)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T22.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T22_large_integral
#print axioms C1T22_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
