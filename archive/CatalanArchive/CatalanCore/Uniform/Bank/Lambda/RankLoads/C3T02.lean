import CatalanCore.Uniform.Bank.Lambda.RankPalette.C3T02
import CatalanCore.Uniform.Bank.Lambda.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankLoads
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
    have he : C3T02.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T02.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T02_cload_5]
    exact rank_castV_ne_zero_of_fst p ((27646144566798850106926380584243 / 32252203580227729735959115607275), (-125867971596035968488506433994681 / 258017628641821837887672924858200)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T02_large_integral
#print axioms C3T02_reduced_loads_nonzero
end CatalanCore.Uniform.Bank.Lambda.RankLoads
