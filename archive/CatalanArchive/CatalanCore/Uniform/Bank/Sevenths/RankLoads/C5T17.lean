import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5T17
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C5T17_small_kills : C5T17.kr.card ≤ 1 ∧ C5T17.kc.card ≤ 1 := by decide +kernel

theorem C5T17_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T17.Integral p := by
  apply C5T17_integral p
  intro hd
  have hpos : 0 < C5T17_den := by decide +kernel
  have hbound : C5T17_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T17_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T17.kr, castV p (C5T17.rload d) ≠ 0) ∧
    (∀ d ∈ C5T17.kc, castV p (C5T17.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T17.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T17.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T17_cload_3]
    exact rank_castV_ne_zero_of_fst p ((88826886444701 / 92941318035340), (-41973208914319 / 23235329508835)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T17_large_integral
#print axioms C5T17_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
