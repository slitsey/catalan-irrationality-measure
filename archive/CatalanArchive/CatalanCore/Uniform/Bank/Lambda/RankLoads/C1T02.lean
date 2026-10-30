import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T02
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T02_small_kills : C1T02.kr.card ≤ 1 ∧ C1T02.kc.card ≤ 1 := by decide +kernel

theorem C1T02_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T02.Integral p := by
  apply C1T02_integral p
  intro hd
  have hpos : 0 < C1T02_den := by decide +kernel
  have hbound : C1T02_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T02_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T02.kr, castV p (C1T02.rload d) ≠ 0) ∧
    (∀ d ∈ C1T02.kc, castV p (C1T02.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T02.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T02.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T02_cload_5]
    exact rank_castV_ne_zero_of_fst p ((11780711059803710029008531100185383 / 11873049637815837540695728305250775), (-21928061945868238216641049838150781763 / 5984017017459182120510647065846390600)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T02_large_integral
#print axioms C1T02_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
