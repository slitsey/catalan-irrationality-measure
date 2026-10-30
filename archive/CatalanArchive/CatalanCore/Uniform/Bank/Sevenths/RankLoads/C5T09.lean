import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5T09
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C5T09_small_kills : C5T09.kr.card ≤ 1 ∧ C5T09.kc.card ≤ 1 := by decide +kernel

theorem C5T09_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T09.Integral p := by
  apply C5T09_integral p
  intro hd
  have hpos : 0 < C5T09_den := by decide +kernel
  have hbound : C5T09_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T09_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T09.kr, castV p (C5T09.rload d) ≠ 0) ∧
    (∀ d ∈ C5T09.kc, castV p (C5T09.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T09.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T09_rload_5]
    exact rank_castV_ne_zero_of_fst p ((438775970875049820257 / 6406403291402927140120), (-7327887412246007402443 / 6406403291402927140120)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T09.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T09_large_integral
#print axioms C5T09_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
