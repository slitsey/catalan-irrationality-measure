import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C9T00
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C9T00_small_kills : C9T00.kr.card ≤ 1 ∧ C9T00.kc.card ≤ 1 := by decide +kernel

theorem C9T00_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T00.Integral p := by
  apply C9T00_integral p
  intro hd
  have hpos : 0 < C9T00_den := by decide +kernel
  have hbound : C9T00_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T00_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T00.kr, castV p (C9T00.rload d) ≠ 0) ∧
    (∀ d ∈ C9T00.kc, castV p (C9T00.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T00.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T00_rload_6]
    exact rank_castV_ne_zero_of_fst p ((160698051091945740838900666066511451019 / 620970870051521735219250583759609371000), (-2640804646404584955300680491933381256041 / 3725825220309130411315503502557656226000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T00.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T00_large_integral
#print axioms C9T00_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
