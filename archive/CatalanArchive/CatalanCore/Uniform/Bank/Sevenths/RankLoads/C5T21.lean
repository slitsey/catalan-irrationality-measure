import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5T21
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C5T21_small_kills : C5T21.kr.card ≤ 1 ∧ C5T21.kc.card ≤ 1 := by decide +kernel

theorem C5T21_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T21.Integral p := by
  apply C5T21_integral p
  intro hd
  have hpos : 0 < C5T21_den := by decide +kernel
  have hbound : C5T21_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T21_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T21.kr, castV p (C5T21.rload d) ≠ 0) ∧
    (∀ d ∈ C5T21.kc, castV p (C5T21.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T21.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T21_rload_3]
    exact rank_castV_ne_zero_of_fst p ((-26467723 / 46883280), (-3676321 / 3906940)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T21.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T21_large_integral
#print axioms C5T21_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
