import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T12
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T12_small_kills : C1T12.kr.card ≤ 1 ∧ C1T12.kc.card ≤ 1 := by decide +kernel

theorem C1T12_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T12.Integral p := by
  apply C1T12_integral p
  intro hd
  have hpos : 0 < C1T12_den := by decide +kernel
  have hbound : C1T12_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T12_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T12.kr, castV p (C1T12.rload d) ≠ 0) ∧
    (∀ d ∈ C1T12.kc, castV p (C1T12.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T12.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T12.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T12_cload_4]
    exact rank_castV_ne_zero_of_fst p ((7520266191241547495046271 / 7533320441904572009947560), (-34180591495347838975550029 / 5022213627936381339965040)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T12_large_integral
#print axioms C1T12_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
