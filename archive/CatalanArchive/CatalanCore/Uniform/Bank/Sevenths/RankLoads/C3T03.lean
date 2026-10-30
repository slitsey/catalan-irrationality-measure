import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3T03
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T03_small_kills : C3T03.kr.card ≤ 1 ∧ C3T03.kc.card ≤ 1 := by decide +kernel

theorem C3T03_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T03.Integral p := by
  apply C3T03_integral p
  intro hd
  have hpos : 0 < C3T03_den := by decide +kernel
  have hbound : C3T03_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T03_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T03.kr, castV p (C3T03.rload d) ≠ 0) ∧
    (∀ d ∈ C3T03.kc, castV p (C3T03.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T03.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T03.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T03_cload_6]
    exact rank_castV_ne_zero_of_fst p ((10588418675440147362036875120874044948683321 / 11973520181454296166988045888204460106796502), (-3660975139320157735123990380212192425909199 / 6301852727081208508941076783265505319366580)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T03_large_integral
#print axioms C3T03_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
