import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3T00
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T00_small_kills : C3T00.kr.card ≤ 1 ∧ C3T00.kc.card ≤ 1 := by decide +kernel

theorem C3T00_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T00.Integral p := by
  apply C3T00_integral p
  intro hd
  have hpos : 0 < C3T00_den := by decide +kernel
  have hbound : C3T00_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T00_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T00.kr, castV p (C3T00.rload d) ≠ 0) ∧
    (∀ d ∈ C3T00.kc, castV p (C3T00.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T00.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T00_rload_6]
    exact rank_castV_ne_zero_of_fst p ((294483208314490275358668570677837 / 1049681878820509310974159666501254), (-1369040334672791665210133746385199 / 3498939596068364369913865555004180)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T00.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T00_large_integral
#print axioms C3T00_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
