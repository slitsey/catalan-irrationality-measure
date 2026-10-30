import CatalanCore.Uniform.Bank.Lambda.RankFibre.C3S07
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T11
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T12
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T13
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T14
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T15
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T16
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankFacts
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
open RankFibre RankData RankLoads
open scoped Classical

theorem C3S07_load_facts (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hp : rankPrimeCutoff < p) (x : ZMod p) :
    let c := C3S07_assignment a p r m s ha hp29 hp4 hrp hm1 x
    (c.kr.card ≤ 1 ∧ c.kc.card ≤ 1) ∧
    (∀ d ∈ c.kr, (c.rload d).1 ∈ S p ∧ (c.rload d).2 ∈ S p) ∧
    (∀ d ∈ c.kc, (c.cload d).1 ∈ S p ∧ (c.cload d).2 ∈ S p ∧ castV p (c.cload d) ≠ 0) := by
  dsimp only
  unfold C3S07_assignment
  split_ifs
  · refine ⟨C3T13_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T13.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T13.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T13_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T13.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T13.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T14_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T14.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T14.kc = {3} := rfl
      have hd' : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C3T14_reduced_loads_nonzero p hp).2 3 hd
      rw [C3T14_cload_3]
      exact ⟨rank_rational_mem p (-2911379 / 8004612 : ℚ) hp (by decide +kernel), rank_rational_mem p (-669611 / 2668204 : ℚ) hp (by decide +kernel), by simpa only [C3T14_cload_3] using hn⟩
  · refine ⟨C3T15_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T15.kr = {3} := rfl
      have hd' : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C3T15_rload_3]
      exact ⟨rank_rational_mem p (-2911379 / 8004612 : ℚ) hp (by decide +kernel), rank_rational_mem p (-669611 / 2668204 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C3T15.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T11_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T11.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T11.kc = {3} := rfl
      have hd' : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C3T11_reduced_loads_nonzero p hp).2 3 hd
      rw [C3T11_cload_3]
      exact ⟨rank_rational_mem p (284721814253 / 348060615364 : ℚ) hp (by decide +kernel), rank_rational_mem p (-4331966659781 / 8701515384100 : ℚ) hp (by decide +kernel), by simpa only [C3T11_cload_3] using hn⟩
  · refine ⟨C3T12_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T12.kr = {3} := rfl
      have hd' : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C3T12_rload_3]
      exact ⟨rank_rational_mem p (284721814253 / 348060615364 : ℚ) hp (by decide +kernel), rank_rational_mem p (-4331966659781 / 8701515384100 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C3T12.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T16_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T16.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T16.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T16_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T16.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T16.kc = ∅ := rfl
      simp [he] at hd
  · simp [trivCert, FibreCert.triv]

#print axioms C3S07_load_facts
end CatalanCore.Uniform.Bank.Lambda.RankFacts
