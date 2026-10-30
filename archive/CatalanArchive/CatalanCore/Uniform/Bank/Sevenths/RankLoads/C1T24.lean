import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T24
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T24_small_kills : C1T24.kr.card ≤ 1 ∧ C1T24.kc.card ≤ 1 := by decide +kernel

theorem C1T24_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T24.Integral p := by
  apply C1T24_integral p
  intro hd
  have hpos : 0 < C1T24_den := by decide +kernel
  have hbound : C1T24_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T24_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T24.kr, castV p (C1T24.rload d) ≠ 0) ∧
    (∀ d ∈ C1T24.kc, castV p (C1T24.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T24.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T24.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T24_cload_2]
    exact rank_castV_ne_zero_of_fst p ((12206183 / 12234240), (-869867 / 127440)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T24_large_integral
#print axioms C1T24_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
