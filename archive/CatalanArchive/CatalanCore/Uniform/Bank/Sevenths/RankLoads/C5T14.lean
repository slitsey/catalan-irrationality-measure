import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5T14
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C5T14_small_kills : C5T14.kr.card ≤ 1 ∧ C5T14.kc.card ≤ 1 := by decide +kernel

theorem C5T14_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T14.Integral p := by
  apply C5T14_integral p
  intro hd
  have hpos : 0 < C5T14_den := by decide +kernel
  have hbound : C5T14_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T14_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T14.kr, castV p (C5T14.rload d) ≠ 0) ∧
    (∀ d ∈ C5T14.kc, castV p (C5T14.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T14.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T14_rload_4]
    exact rank_castV_ne_zero_of_fst p ((-27334535430997 / 175045825432240), (-37058845307039 / 35009165086448)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T14.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T14_large_integral
#print axioms C5T14_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
