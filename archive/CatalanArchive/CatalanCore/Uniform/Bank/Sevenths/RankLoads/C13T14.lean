import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C13T14
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C13T14_small_kills : C13T14.kr.card ≤ 1 ∧ C13T14.kc.card ≤ 1 := by decide +kernel

theorem C13T14_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T14.Integral p := by
  apply C13T14_integral p
  intro hd
  have hpos : 0 < C13T14_den := by decide +kernel
  have hbound : C13T14_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T14_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T14.kr, castV p (C13T14.rload d) ≠ 0) ∧
    (∀ d ∈ C13T14.kc, castV p (C13T14.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T14.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T14_rload_4]
    exact rank_castV_ne_zero_of_fst p ((-597592459 / 55304875080), (-34258419 / 236345620)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T14.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T14_large_integral
#print axioms C13T14_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
