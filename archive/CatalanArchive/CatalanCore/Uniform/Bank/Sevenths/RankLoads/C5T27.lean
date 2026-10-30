import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5T27
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C5T27_small_kills : C5T27.kr.card ≤ 1 ∧ C5T27.kc.card ≤ 1 := by decide +kernel

theorem C5T27_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T27.Integral p := by
  apply C5T27_integral p
  intro hd
  have hpos : 0 < C5T27_den := by decide +kernel
  have hbound : C5T27_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T27_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T27.kr, castV p (C5T27.rload d) ≠ 0) ∧
    (∀ d ∈ C5T27.kc, castV p (C5T27.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T27.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T27_rload_2]
    exact rank_castV_ne_zero_of_fst p ((-197 / 120), (-23 / 30)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T27.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T27_large_integral
#print axioms C5T27_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
