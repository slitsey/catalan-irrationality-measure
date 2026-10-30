import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5T30
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C5T30_small_kills : C5T30.kr.card ≤ 1 ∧ C5T30.kc.card ≤ 1 := by decide +kernel

theorem C5T30_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T30.Integral p := by
  apply C5T30_integral p
  intro hd
  have hpos : 0 < C5T30_den := by decide +kernel
  have hbound : C5T30_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T30_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T30.kr, castV p (C5T30.rload d) ≠ 0) ∧
    (∀ d ∈ C5T30.kc, castV p (C5T30.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T30.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T30.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T30_cload_1]
    exact rank_castV_ne_zero_of_fst p ((463 / 490), (-40 / 21)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T30_large_integral
#print axioms C5T30_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
