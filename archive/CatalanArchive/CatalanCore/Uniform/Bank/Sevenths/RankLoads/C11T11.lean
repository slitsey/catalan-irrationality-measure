import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C11T11
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C11T11_small_kills : C11T11.kr.card ≤ 1 ∧ C11T11.kc.card ≤ 1 := by decide +kernel

theorem C11T11_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T11.Integral p := by
  apply C11T11_integral p
  intro hd
  have hpos : 0 < C11T11_den := by decide +kernel
  have hbound : C11T11_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T11_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T11.kr, castV p (C11T11.rload d) ≠ 0) ∧
    (∀ d ∈ C11T11.kc, castV p (C11T11.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T11.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T11_rload_4]
    exact rank_castV_ne_zero_of_fst p ((194367277593143842371 / 196874370936942623680), (-1108000516289251149401 / 354373867686496722624)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T11.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T11_large_integral
#print axioms C11T11_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
