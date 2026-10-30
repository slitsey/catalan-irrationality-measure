import CatalanCore.Uniform.Bank.Lambda.RankFibre.C1S12
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T17
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T18
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T20
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T21
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T22
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T23
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T24
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankFacts
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
open RankFibre RankData RankLoads
open scoped Classical

theorem C1S12_load_facts (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hp : rankPrimeCutoff < p) (x : ZMod p) :
    let c := C1S12_assignment a p r m s ha hp29 hp4 hrp hm1 x
    (c.kr.card ≤ 1 ∧ c.kc.card ≤ 1) ∧
    (∀ d ∈ c.kr, (c.rload d).1 ∈ S p ∧ (c.rload d).2 ∈ S p) ∧
    (∀ d ∈ c.kc, (c.cload d).1 ∈ S p ∧ (c.cload d).2 ∈ S p ∧ castV p (c.cload d) ≠ 0) := by
  dsimp only
  unfold C1S12_assignment
  split_ifs
  · refine ⟨C1T21_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T21.kr = {2} := rfl
      have hd' : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C1T21_rload_2]
      exact ⟨rank_rational_mem p (-12 / 5 : ℚ) hp (by decide +kernel), rank_rational_mem p (-33 / 20 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C1T21.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T22_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T22.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T22.kc = {2} := rfl
      have hd' : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C1T22_reduced_loads_nonzero p hp).2 2 hd
      rw [C1T22_cload_2]
      exact ⟨rank_rational_mem p (-12 / 5 : ℚ) hp (by decide +kernel), rank_rational_mem p (-33 / 20 : ℚ) hp (by decide +kernel), by simpa only [C1T22_cload_2] using hn⟩
  · refine ⟨C1T17_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T17.kr = {2} := rfl
      have hd' : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C1T17_rload_2]
      exact ⟨rank_rational_mem p (92756 / 93825 : ℚ) hp (by decide +kernel), rank_rational_mem p (-92563 / 25020 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C1T17.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T18_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T18.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T18.kc = {2} := rfl
      have hd' : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C1T18_reduced_loads_nonzero p hp).2 2 hd
      rw [C1T18_cload_2]
      exact ⟨rank_rational_mem p (92756 / 93825 : ℚ) hp (by decide +kernel), rank_rational_mem p (-92563 / 25020 : ℚ) hp (by decide +kernel), by simpa only [C1T18_cload_2] using hn⟩
  · refine ⟨C1T20_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T20.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T20.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T20_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T20.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T20.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T23_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T23.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T23.kc = {1} := rfl
      have hd' : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C1T23_reduced_loads_nonzero p hp).2 1 hd
      rw [C1T23_cload_1]
      exact ⟨rank_rational_mem p (79 / 80 : ℚ) hp (by decide +kernel), rank_rational_mem p (-15 / 4 : ℚ) hp (by decide +kernel), by simpa only [C1T23_cload_1] using hn⟩
  · refine ⟨C1T24_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T24.kr = {1} := rfl
      have hd' : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C1T24_rload_1]
      exact ⟨rank_rational_mem p (79 / 80 : ℚ) hp (by decide +kernel), rank_rational_mem p (-15 / 4 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C1T24.kc = ∅ := rfl
      simp [he] at hd
  · simp [trivCert, FibreCert.triv]

#print axioms C1S12_load_facts
end CatalanCore.Uniform.Bank.Lambda.RankFacts
