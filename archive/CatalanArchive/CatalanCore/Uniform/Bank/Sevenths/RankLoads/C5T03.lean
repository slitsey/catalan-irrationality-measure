import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5T03
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C5T03_small_kills : C5T03.kr.card ≤ 1 ∧ C5T03.kc.card ≤ 1 := by decide +kernel

theorem C5T03_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T03.Integral p := by
  apply C5T03_integral p
  intro hd
  have hpos : 0 < C5T03_den := by decide +kernel
  have hbound : C5T03_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T03_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T03.kr, castV p (C5T03.rload d) ≠ 0) ∧
    (∀ d ∈ C5T03.kc, castV p (C5T03.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T03.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T03.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T03_cload_6]
    exact rank_castV_ne_zero_of_fst p ((44937261743829484335362526866014588927699013017 / 46408277013154567295820860566182756770141768064), (-82843324323017664427375250907837778036718237777 / 46408277013154567295820860566182756770141768064)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T03_large_integral
#print axioms C5T03_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
