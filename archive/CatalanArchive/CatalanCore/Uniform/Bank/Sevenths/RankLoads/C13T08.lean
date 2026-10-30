import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C13T08
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C13T08_small_kills : C13T08.kr.card ≤ 1 ∧ C13T08.kc.card ≤ 1 := by decide +kernel

theorem C13T08_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T08.Integral p := by
  apply C13T08_integral p
  intro hd
  have hpos : 0 < C13T08_den := by decide +kernel
  have hbound : C13T08_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T08_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T08.kr, castV p (C13T08.rload d) ≠ 0) ∧
    (∀ d ∈ C13T08.kc, castV p (C13T08.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T08.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T08.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T08_cload_5]
    exact rank_castV_ne_zero_of_fst p ((16145126832533680037 / 94056030380121147000), (-380708984950188733 / 2411693086669773000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T08_large_integral
#print axioms C13T08_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
