import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C13T19
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C13T19_small_kills : C13T19.kr.card ≤ 1 ∧ C13T19.kc.card ≤ 1 := by decide +kernel

theorem C13T19_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T19.Integral p := by
  apply C13T19_integral p
  intro hd
  have hpos : 0 < C13T19_den := by decide +kernel
  have hbound : C13T19_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T19_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T19.kr, castV p (C13T19.rload d) ≠ 0) ∧
    (∀ d ∈ C13T19.kc, castV p (C13T19.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T19.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T19_rload_3]
    exact rank_castV_ne_zero_of_fst p ((8924952966103 / 11820280388670), (-993366669781 / 3940093462890)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T19.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T19_large_integral
#print axioms C13T19_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
