import CatalanCore.Uniform.Bank.Lambda.RankPalette.C1T05
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T05_small_kills : C1T05.kr.card ≤ 1 ∧ C1T05.kc.card ≤ 1 := by decide +kernel

theorem C1T05_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T05.Integral p := by
  apply C1T05_integral p
  intro hd
  have hpos : 0 < C1T05_den := by decide +kernel
  have hbound : C1T05_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T05_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T05.kr, castV p (C1T05.rload d) ≠ 0) ∧
    (∀ d ∈ C1T05.kc, castV p (C1T05.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T05.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T05_rload_4]
    exact rank_castV_ne_zero_of_fst p ((71682429623312519612552 / 72312978015906865267095), (-707739483381693894634471 / 192834608042418307378920)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T05.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T05_large_integral
#print axioms C1T05_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
