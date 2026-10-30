import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3T02
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C3T02_small_kills : C3T02.kr.card ≤ 1 ∧ C3T02.kc.card ≤ 1 := by decide +kernel

theorem C3T02_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T02.Integral p := by
  apply C3T02_integral p
  intro hd
  have hpos : 0 < C3T02_den := by decide +kernel
  have hbound : C3T02_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T02_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T02.kr, castV p (C3T02.rload d) ≠ 0) ∧
    (∀ d ∈ C3T02.kc, castV p (C3T02.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T02.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T02_rload_6]
    exact rank_castV_ne_zero_of_fst p ((10588418675440147362036875120874044948683321 / 11973520181454296166988045888204460106796502), (-3660975139320157735123990380212192425909199 / 6301852727081208508941076783265505319366580)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T02.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T02_large_integral
#print axioms C3T02_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
