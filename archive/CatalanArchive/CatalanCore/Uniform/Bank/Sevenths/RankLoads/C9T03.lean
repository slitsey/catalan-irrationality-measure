import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C9T03
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C9T03_small_kills : C9T03.kr.card ≤ 1 ∧ C9T03.kc.card ≤ 1 := by decide +kernel

theorem C9T03_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T03.Integral p := by
  apply C9T03_integral p
  intro hd
  have hpos : 0 < C9T03_den := by decide +kernel
  have hbound : C9T03_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T03_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T03.kr, castV p (C9T03.rload d) ≠ 0) ∧
    (∀ d ∈ C9T03.kc, castV p (C9T03.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T03.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T03.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T03_cload_6]
    exact rank_castV_ne_zero_of_fst p ((797245704292218020143124714204509304912334432342707 / 854850861404880227492362066261940112446375566083000), (-5413966266810456649582988012474527489847262950579873 / 5129105168429281364954172397571640674678253396498000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T03_large_integral
#print axioms C9T03_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
