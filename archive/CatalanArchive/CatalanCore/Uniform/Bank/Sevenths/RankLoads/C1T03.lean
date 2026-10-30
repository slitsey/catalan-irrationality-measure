import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T03
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T03_small_kills : C1T03.kr.card ≤ 1 ∧ C1T03.kc.card ≤ 1 := by decide +kernel

theorem C1T03_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T03.Integral p := by
  apply C1T03_integral p
  intro hd
  have hpos : 0 < C1T03_den := by decide +kernel
  have hbound : C1T03_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T03_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T03.kr, castV p (C1T03.rload d) ≠ 0) ∧
    (∀ d ∈ C1T03.kc, castV p (C1T03.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T03.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T03.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T03_cload_6]
    exact rank_castV_ne_zero_of_fst p ((4636750447571997559221060361775872780732963408494446 / 4643193594935921891088267681836784305796698716941375), (-757642551055354749996506551595817222881370572249524909 / 111436646278462125386118424364082823339120769206593000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T03_large_integral
#print axioms C1T03_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
