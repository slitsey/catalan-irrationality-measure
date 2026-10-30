import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5T18
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C5T18_small_kills : C5T18.kr.card ≤ 1 ∧ C5T18.kc.card ≤ 1 := by decide +kernel

theorem C5T18_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T18.Integral p := by
  apply C5T18_integral p
  intro hd
  have hpos : 0 < C5T18_den := by decide +kernel
  have hbound : C5T18_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T18_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T18.kr, castV p (C5T18.rload d) ≠ 0) ∧
    (∀ d ∈ C5T18.kc, castV p (C5T18.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T18.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T18_rload_3]
    exact rank_castV_ne_zero_of_fst p ((88826886444701 / 92941318035340), (-41973208914319 / 23235329508835)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T18.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T18_large_integral
#print axioms C5T18_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
