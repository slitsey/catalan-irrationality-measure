import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C9T26
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C9T26_small_kills : C9T26.kr.card ≤ 1 ∧ C9T26.kc.card ≤ 1 := by decide +kernel

theorem C9T26_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T26.Integral p := by
  apply C9T26_integral p
  intro hd
  have hpos : 0 < C9T26_den := by decide +kernel
  have hbound : C9T26_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T26_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T26.kr, castV p (C9T26.rload d) ≠ 0) ∧
    (∀ d ∈ C9T26.kc, castV p (C9T26.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T26.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T26_rload_2]
    exact rank_castV_ne_zero_of_fst p ((-123 / 88), (-39 / 88)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T26.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T26_large_integral
#print axioms C9T26_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
