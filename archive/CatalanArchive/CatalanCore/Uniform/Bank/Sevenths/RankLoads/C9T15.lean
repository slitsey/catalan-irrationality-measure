import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C9T15
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C9T15_small_kills : C9T15.kr.card ≤ 1 ∧ C9T15.kc.card ≤ 1 := by decide +kernel

theorem C9T15_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T15.Integral p := by
  apply C9T15_integral p
  intro hd
  have hpos : 0 < C9T15_den := by decide +kernel
  have hbound : C9T15_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T15_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T15.kr, castV p (C9T15.rload d) ≠ 0) ∧
    (∀ d ∈ C9T15.kc, castV p (C9T15.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T15.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T15.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T15_cload_4]
    exact rank_castV_ne_zero_of_fst p ((-11868940030333 / 156622051398582), (-1611490998685361 / 2610367523309700)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T15_large_integral
#print axioms C9T15_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
