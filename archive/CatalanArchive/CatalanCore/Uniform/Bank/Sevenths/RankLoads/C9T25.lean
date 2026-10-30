import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C9T25
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C9T25_small_kills : C9T25.kr.card ≤ 1 ∧ C9T25.kc.card ≤ 1 := by decide +kernel

theorem C9T25_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T25.Integral p := by
  apply C9T25_integral p
  intro hd
  have hpos : 0 < C9T25_den := by decide +kernel
  have hbound : C9T25_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T25_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T25.kr, castV p (C9T25.rload d) ≠ 0) ∧
    (∀ d ∈ C9T25.kc, castV p (C9T25.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T25.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T25.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T25_cload_2]
    exact rank_castV_ne_zero_of_fst p ((6772225 / 7589241), (-1011251 / 919908)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T25_large_integral
#print axioms C9T25_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
