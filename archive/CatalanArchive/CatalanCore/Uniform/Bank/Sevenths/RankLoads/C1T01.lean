import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T01
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T01_small_kills : C1T01.kr.card ≤ 1 ∧ C1T01.kc.card ≤ 1 := by decide +kernel

theorem C1T01_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T01.Integral p := by
  apply C1T01_integral p
  intro hd
  have hpos : 0 < C1T01_den := by decide +kernel
  have hbound : C1T01_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T01_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T01.kr, castV p (C1T01.rload d) ≠ 0) ∧
    (∀ d ∈ C1T01.kc, castV p (C1T01.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T01.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T01.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T01_cload_6]
    exact rank_castV_ne_zero_of_fst p ((-1427790115970909280998634104325747868808 / 5454674359830046949033009432616846411125), (-1902208755681645118418120850728652548272049 / 392736553907763380330376679148412941601000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T01_large_integral
#print axioms C1T01_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
