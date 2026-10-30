import CatalanCore.Uniform.Bank.Lambda.RankPalette.C3T01
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T01_small_kills : C3T01.kr.card ≤ 1 ∧ C3T01.kc.card ≤ 1 := by decide +kernel

theorem C3T01_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T01.Integral p := by
  apply C3T01_integral p
  intro hd
  have hpos : 0 < C3T01_den := by decide +kernel
  have hbound : C3T01_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T01_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T01.kr, castV p (C3T01.rload d) ≠ 0) ∧
    (∀ d ∈ C3T01.kc, castV p (C3T01.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T01.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T01_rload_5]
    exact rank_castV_ne_zero_of_fst p ((58040617587411647653 / 360543338619249332525), (-6247154238882597275657 / 20190426962677962621400)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T01.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T01_large_integral
#print axioms C3T01_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
