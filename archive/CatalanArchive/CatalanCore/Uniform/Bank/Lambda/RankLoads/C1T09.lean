import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T09
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T09_small_kills : C1T09.kr.card ≤ 1 ∧ C1T09.kc.card ≤ 1 := by decide +kernel

theorem C1T09_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T09.Integral p := by
  apply C1T09_integral p
  intro hd
  have hpos : 0 < C1T09_den := by decide +kernel
  have hbound : C1T09_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T09_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T09.kr, castV p (C1T09.rload d) ≠ 0) ∧
    (∀ d ∈ C1T09.kc, castV p (C1T09.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T09.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T09.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T09_cload_4]
    exact rank_castV_ne_zero_of_fst p ((-1923630295976 / 4570623985005), (-257538007361335 / 114570307890792)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T09_large_integral
#print axioms C1T09_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
