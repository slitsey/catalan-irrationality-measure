import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3T06
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T06_small_kills : C3T06.kr.card ≤ 1 ∧ C3T06.kc.card ≤ 1 := by decide +kernel

theorem C3T06_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T06.Integral p := by
  apply C3T06_integral p
  intro hd
  have hpos : 0 < C3T06_den := by decide +kernel
  have hbound : C3T06_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T06_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T06.kr, castV p (C3T06.rload d) ≠ 0) ∧
    (∀ d ∈ C3T06.kc, castV p (C3T06.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T06.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T06_rload_5]
    exact rank_castV_ne_zero_of_fst p ((203496165588974891691696208082477 / 233299340887025959804754923014874), (-1358574380542247014514767217895147 / 2332993408870259598047549230148740)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T06.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T06_large_integral
#print axioms C3T06_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
