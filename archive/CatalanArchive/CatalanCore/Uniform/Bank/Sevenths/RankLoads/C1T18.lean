import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T18
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T18_small_kills : C1T18.kr.card ≤ 1 ∧ C1T18.kc.card ≤ 1 := by decide +kernel

theorem C1T18_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T18.Integral p := by
  apply C1T18_integral p
  intro hd
  have hpos : 0 < C1T18_den := by decide +kernel
  have hbound : C1T18_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T18_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T18.kr, castV p (C1T18.rload d) ≠ 0) ∧
    (∀ d ∈ C1T18.kc, castV p (C1T18.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T18.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T18_rload_3]
    exact rank_castV_ne_zero_of_fst p ((47126631993233 / 47220172986690), (-1286798649003677 / 188880691946760)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T18.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T18_large_integral
#print axioms C1T18_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
