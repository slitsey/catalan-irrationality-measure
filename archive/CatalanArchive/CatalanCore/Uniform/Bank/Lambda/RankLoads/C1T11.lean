import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T11
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T11_small_kills : C1T11.kr.card ≤ 1 ∧ C1T11.kc.card ≤ 1 := by decide +kernel

theorem C1T11_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T11.Integral p := by
  apply C1T11_integral p
  intro hd
  have hpos : 0 < C1T11_den := by decide +kernel
  have hbound : C1T11_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T11_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T11.kr, castV p (C1T11.rload d) ≠ 0) ∧
    (∀ d ∈ C1T11.kc, castV p (C1T11.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T11.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T11.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T11_cload_3]
    exact rank_castV_ne_zero_of_fst p ((2439392450783 / 2463829399980), (-9066989195663 / 2463829399980)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T11_large_integral
#print axioms C1T11_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
