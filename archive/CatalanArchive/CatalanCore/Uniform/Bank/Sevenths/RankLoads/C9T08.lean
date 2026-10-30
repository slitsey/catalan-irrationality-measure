import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C9T08
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C9T08_small_kills : C9T08.kr.card ≤ 1 ∧ C9T08.kc.card ≤ 1 := by decide +kernel

theorem C9T08_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T08.Integral p := by
  apply C9T08_integral p
  intro hd
  have hpos : 0 < C9T08_den := by decide +kernel
  have hbound : C9T08_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T08_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T08.kr, castV p (C9T08.rload d) ≠ 0) ∧
    (∀ d ∈ C9T08.kc, castV p (C9T08.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T08.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T08.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T08_cload_5]
    exact rank_castV_ne_zero_of_fst p ((64595300400589858614263297 / 508723922290294453028913000), (-226912852446535843071198047 / 339149281526862968685942000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T08_large_integral
#print axioms C9T08_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
