import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1T16
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C1T16_small_kills : C1T16.kr.card ≤ 1 ∧ C1T16.kc.card ≤ 1 := by decide +kernel

theorem C1T16_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T16.Integral p := by
  apply C1T16_integral p
  intro hd
  have hpos : 0 < C1T16_den := by decide +kernel
  have hbound : C1T16_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T16_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T16.kr, castV p (C1T16.rload d) ≠ 0) ∧
    (∀ d ∈ C1T16.kc, castV p (C1T16.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T16.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T16.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T16_cload_4]
    exact rank_castV_ne_zero_of_fst p ((-796007066211827 / 845782648686360), (-2424410564966207 / 563855099124240)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T16_large_integral
#print axioms C1T16_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
