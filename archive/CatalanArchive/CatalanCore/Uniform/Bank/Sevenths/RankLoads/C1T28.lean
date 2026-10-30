import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T28
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T28_small_kills : C1T28.kr.card ≤ 1 ∧ C1T28.kc.card ≤ 1 := by decide +kernel

theorem C1T28_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T28.Integral p := by
  apply C1T28_integral p
  intro hd
  have hpos : 0 < C1T28_den := by decide +kernel
  have hbound : C1T28_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T28_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T28.kr, castV p (C1T28.rload d) ≠ 0) ∧
    (∀ d ∈ C1T28.kc, castV p (C1T28.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T28.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T28.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T28_cload_2]
    exact rank_castV_ne_zero_of_fst p ((-123 / 32), (-51 / 16)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T28_large_integral
#print axioms C1T28_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
