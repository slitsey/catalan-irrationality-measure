import CatalanCore.Uniform.Bank.Lambda.RankPalette.C3T08
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T08_small_kills : C3T08.kr.card ≤ 1 ∧ C3T08.kc.card ≤ 1 := by decide +kernel

theorem C3T08_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T08.Integral p := by
  apply C3T08_integral p
  intro hd
  have hpos : 0 < C3T08_den := by decide +kernel
  have hbound : C3T08_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T08_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T08.kr, castV p (C3T08.rload d) ≠ 0) ∧
    (∀ d ∈ C3T08.kc, castV p (C3T08.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T08.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T08_rload_4]
    exact rank_castV_ne_zero_of_fst p ((-15734175008 / 581539134407), (-6619969800313 / 23261565376280)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T08.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T08_large_integral
#print axioms C3T08_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
