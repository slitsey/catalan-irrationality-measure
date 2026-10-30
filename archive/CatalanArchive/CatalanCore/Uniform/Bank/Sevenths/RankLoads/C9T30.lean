import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C9T30
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C9T30_small_kills : C9T30.kr.card ≤ 1 ∧ C9T30.kc.card ≤ 1 := by decide +kernel

theorem C9T30_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T30.Integral p := by
  apply C9T30_integral p
  intro hd
  have hpos : 0 < C9T30_den := by decide +kernel
  have hbound : C9T30_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T30_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T30.kr, castV p (C9T30.rload d) ≠ 0) ∧
    (∀ d ∈ C9T30.kc, castV p (C9T30.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T30.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T30.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T30_cload_1]
    exact rank_castV_ne_zero_of_fst p ((475 / 539), (-33 / 28)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T30_large_integral
#print axioms C9T30_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
