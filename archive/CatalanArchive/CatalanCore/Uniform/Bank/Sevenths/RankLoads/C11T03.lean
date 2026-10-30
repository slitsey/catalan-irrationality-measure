import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C11T03
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C11T03_small_kills : C11T03.kr.card ≤ 1 ∧ C11T03.kc.card ≤ 1 := by decide +kernel

theorem C11T03_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T03.Integral p := by
  apply C11T03_integral p
  intro hd
  have hpos : 0 < C11T03_den := by decide +kernel
  have hbound : C11T03_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T03_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T03.kr, castV p (C11T03.rload d) ≠ 0) ∧
    (∀ d ∈ C11T03.kc, castV p (C11T03.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T03.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T03.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T03_cload_6]
    exact rank_castV_ne_zero_of_fst p ((3391572296869121202111865280724867708815855357021 / 3426793831761318384959429683271737419060419437950), (-256337449464092121877671051100641355269307605256397 / 82243051962271641239026312398521698057450066510800)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T03_large_integral
#print axioms C11T03_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
