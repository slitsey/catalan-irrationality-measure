import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C9T05
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C9T05_small_kills : C9T05.kr.card ≤ 1 ∧ C9T05.kc.card ≤ 1 := by decide +kernel

theorem C9T05_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T05.Integral p := by
  apply C9T05_integral p
  intro hd
  have hpos : 0 < C9T05_den := by decide +kernel
  have hbound : C9T05_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T05_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T05.kr, castV p (C9T05.rload d) ≠ 0) ∧
    (∀ d ∈ C9T05.kc, castV p (C9T05.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T05.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T05.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T05_cload_5]
    exact rank_castV_ne_zero_of_fst p ((749952733977325523646269837998889873 / 810189578445930845012869753666217000), (-15431064562369921674403797899409240821 / 14583412412026755210231655565991906000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T05_large_integral
#print axioms C9T05_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
