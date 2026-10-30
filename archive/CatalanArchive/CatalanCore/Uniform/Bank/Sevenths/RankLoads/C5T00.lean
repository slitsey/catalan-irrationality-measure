import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5T00
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C5T00_small_kills : C5T00.kr.card ≤ 1 ∧ C5T00.kc.card ≤ 1 := by decide +kernel

theorem C5T00_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T00.Integral p := by
  apply C5T00_integral p
  intro hd
  have hpos : 0 < C5T00_den := by decide +kernel
  have hbound : C5T00_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T00_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T00.kr, castV p (C5T00.rload d) ≠ 0) ∧
    (∀ d ∈ C5T00.kc, castV p (C5T00.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T00.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T00_rload_6]
    exact rank_castV_ne_zero_of_fst p ((230471884324722397994169594074547 / 1079406927775970636862169002845120), (-652466848665211800897598990869389 / 539703463887985318431084501422560)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T00.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T00_large_integral
#print axioms C5T00_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
