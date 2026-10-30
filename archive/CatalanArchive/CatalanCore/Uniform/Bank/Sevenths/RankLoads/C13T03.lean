import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C13T03
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C13T03_small_kills : C13T03.kr.card ≤ 1 ∧ C13T03.kc.card ≤ 1 := by decide +kernel

theorem C13T03_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T03.Integral p := by
  apply C13T03_integral p
  intro hd
  have hpos : 0 < C13T03_den := by decide +kernel
  have hbound : C13T03_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T03_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T03.kr, castV p (C13T03.rload d) ≠ 0) ∧
    (∀ d ∈ C13T03.kc, castV p (C13T03.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T03.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T03.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T03_cload_6]
    exact rank_castV_ne_zero_of_fst p ((6781764726127563921518437768951415485808160811 / 8195140102591842847975581774647508295351852500), (-3808678665034229636448146109902714673314709083 / 15479709082673480935064987796556404557886832500)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T03_large_integral
#print axioms C13T03_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
