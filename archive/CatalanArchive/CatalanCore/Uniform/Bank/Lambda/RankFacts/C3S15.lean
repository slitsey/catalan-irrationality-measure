import CatalanCore.Uniform.Bank.Lambda.RankFibre.C3S15
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T23
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T24
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T25
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T26
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T27
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T28
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankFacts
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
open RankFibre RankData RankLoads
open scoped Classical

theorem C3S15_load_facts (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hp : rankPrimeCutoff < p) (x : ZMod p) :
    let c := C3S15_assignment a p r m s ha hp29 hp4 hrp hm1 x
    (c.kr.card ≤ 1 ∧ c.kc.card ≤ 1) ∧
    (∀ d ∈ c.kr, (c.rload d).1 ∈ S p ∧ (c.rload d).2 ∈ S p) ∧
    (∀ d ∈ c.kc, (c.cload d).1 ∈ S p ∧ (c.cload d).2 ∈ S p ∧ castV p (c.cload d) ≠ 0) := by
  dsimp only
  unfold C3S15_assignment
  split_ifs
  · refine ⟨C3T23_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T23.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T23.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T23_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T23.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T23.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T26_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T26.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T26.kc = {1} := rfl
      have hd' : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C3T26_reduced_loads_nonzero p hp).2 1 hd
      rw [C3T26_cload_1]
      exact ⟨rank_rational_mem p (1 / 1 : ℚ) hp (by decide +kernel), rank_rational_mem p (0 / 1 : ℚ) hp (by decide +kernel), by simpa only [C3T26_cload_1] using hn⟩
  · refine ⟨C3T27_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T27.kr = {1} := rfl
      have hd' : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C3T27_rload_1]
      exact ⟨rank_rational_mem p (1 / 1 : ℚ) hp (by decide +kernel), rank_rational_mem p (0 / 1 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C3T27.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T24_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T24.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T24.kc = {1} := rfl
      have hd' : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C3T24_reduced_loads_nonzero p hp).2 1 hd
      rw [C3T24_cload_1]
      exact ⟨rank_rational_mem p (85 / 112 : ℚ) hp (by decide +kernel), rank_rational_mem p (-7 / 12 : ℚ) hp (by decide +kernel), by simpa only [C3T24_cload_1] using hn⟩
  · refine ⟨C3T25_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T25.kr = {1} := rfl
      have hd' : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C3T25_rload_1]
      exact ⟨rank_rational_mem p (85 / 112 : ℚ) hp (by decide +kernel), rank_rational_mem p (-7 / 12 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C3T25.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T28_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T28.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T28.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T28_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T28.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T28.kc = ∅ := rfl
      simp [he] at hd
  · simp [trivCert, FibreCert.triv]

#print axioms C3S15_load_facts
end CatalanCore.Uniform.Bank.Lambda.RankFacts
