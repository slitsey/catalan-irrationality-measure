import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C9T11
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C9T11_small_kills : C9T11.kr.card ≤ 1 ∧ C9T11.kc.card ≤ 1 := by decide +kernel

theorem C9T11_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T11.Integral p := by
  apply C9T11_integral p
  intro hd
  have hpos : 0 < C9T11_den := by decide +kernel
  have hbound : C9T11_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T11_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T11.kr, castV p (C9T11.rload d) ≠ 0) ∧
    (∀ d ∈ C9T11.kc, castV p (C9T11.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T11.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T11_rload_4]
    exact rank_castV_ne_zero_of_fst p ((9451529343565843884853453 / 10307518079936754339016200), (-26568030354499583284849 / 24987922618028495367312)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T11.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T11_large_integral
#print axioms C9T11_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
