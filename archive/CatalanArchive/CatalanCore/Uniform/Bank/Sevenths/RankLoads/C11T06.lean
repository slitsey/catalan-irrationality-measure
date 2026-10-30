import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C11T06
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C11T06_small_kills : C11T06.kr.card ≤ 1 ∧ C11T06.kc.card ≤ 1 := by decide +kernel

theorem C11T06_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T06.Integral p := by
  apply C11T06_integral p
  intro hd
  have hpos : 0 < C11T06_den := by decide +kernel
  have hbound : C11T06_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T06_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T06.kr, castV p (C11T06.rload d) ≠ 0) ∧
    (∀ d ∈ C11T06.kc, castV p (C11T06.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T06.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T06_rload_5]
    exact rank_castV_ne_zero_of_fst p ((1859424937291948945448943332369863 / 1880807400945288216403072781720000), (-10564709708391898345922033865398593 / 3385453321701518789525531007096000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T06.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T06_large_integral
#print axioms C11T06_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
