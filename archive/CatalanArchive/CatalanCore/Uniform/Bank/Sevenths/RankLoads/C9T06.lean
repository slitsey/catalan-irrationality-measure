import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C9T06
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData

theorem C9T06_small_kills : C9T06.kr.card ≤ 1 ∧ C9T06.kc.card ≤ 1 := by decide +kernel

theorem C9T06_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T06.Integral p := by
  apply C9T06_integral p
  intro hd
  have hpos : 0 < C9T06_den := by decide +kernel
  have hbound : C9T06_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T06_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T06.kr, castV p (C9T06.rload d) ≠ 0) ∧
    (∀ d ∈ C9T06.kc, castV p (C9T06.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T06.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T06_rload_5]
    exact rank_castV_ne_zero_of_fst p ((749952733977325523646269837998889873 / 810189578445930845012869753666217000), (-15431064562369921674403797899409240821 / 14583412412026755210231655565991906000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T06.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T06_large_integral
#print axioms C9T06_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Sevenths.RankLoads
