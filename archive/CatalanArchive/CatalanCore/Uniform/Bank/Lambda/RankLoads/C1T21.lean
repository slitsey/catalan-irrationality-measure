import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T21
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T21_small_kills : C1T21.kr.card ≤ 1 ∧ C1T21.kc.card ≤ 1 := by decide +kernel

theorem C1T21_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T21.Integral p := by
  apply C1T21_integral p
  intro hd
  have hpos : 0 < C1T21_den := by decide +kernel
  have hbound : C1T21_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T21_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T21.kr, castV p (C1T21.rload d) ≠ 0) ∧
    (∀ d ∈ C1T21.kc, castV p (C1T21.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T21.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T21_rload_2]
    exact rank_castV_ne_zero_of_fst p ((-12 / 5), (-33 / 20)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T21.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T21_large_integral
#print axioms C1T21_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
