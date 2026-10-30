import CatalanCore.Uniform.Bank.Lambda.RankPalette.C3T00
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T00_small_kills : C3T00.kr.card ≤ 1 ∧ C3T00.kc.card ≤ 1 := by decide +kernel

theorem C3T00_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T00.Integral p := by
  apply C3T00_integral p
  intro hd
  have hpos : 0 < C3T00_den := by decide +kernel
  have hbound : C3T00_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T00_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T00.kr, castV p (C3T00.rload d) ≠ 0) ∧
    (∀ d ∈ C3T00.kc, castV p (C3T00.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T00.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T00.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T00_cload_5]
    exact rank_castV_ne_zero_of_fst p ((58040617587411647653 / 360543338619249332525), (-6247154238882597275657 / 20190426962677962621400)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T00_large_integral
#print axioms C3T00_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
