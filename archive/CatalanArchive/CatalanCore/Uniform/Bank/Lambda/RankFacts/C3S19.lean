import CatalanCore.Uniform.Bank.Lambda.RankFibre.C3S19
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T29
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T30
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T31
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T32
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T33
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankFacts
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
open RankFibre RankData RankLoads
open scoped Classical

theorem C3S19_load_facts (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hp : rankPrimeCutoff < p) (x : ZMod p) :
    let c := C3S19_assignment a p r m s ha hp29 hp4 hrp hm1 x
    (c.kr.card ≤ 1 ∧ c.kc.card ≤ 1) ∧
    (∀ d ∈ c.kr, (c.rload d).1 ∈ S p ∧ (c.rload d).2 ∈ S p) ∧
    (∀ d ∈ c.kc, (c.cload d).1 ∈ S p ∧ (c.cload d).2 ∈ S p ∧ castV p (c.cload d) ≠ 0) := by
  dsimp only
  unfold C3S19_assignment
  split_ifs
  · refine ⟨C3T29_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T29.kr = {0} := rfl
      have hd' : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C3T29_rload_0]
      exact ⟨rank_rational_mem p (1 / 1 : ℚ) hp (by decide +kernel), rank_rational_mem p (0 / 1 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C3T29.kc = {0} := rfl
      have hd' : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C3T29_reduced_loads_nonzero p hp).2 0 hd
      rw [C3T29_cload_0]
      exact ⟨rank_rational_mem p (1 / 1 : ℚ) hp (by decide +kernel), rank_rational_mem p (0 / 1 : ℚ) hp (by decide +kernel), by simpa only [C3T29_cload_0] using hn⟩
  · refine ⟨C3T29_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T29.kr = {0} := rfl
      have hd' : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C3T29_rload_0]
      exact ⟨rank_rational_mem p (1 / 1 : ℚ) hp (by decide +kernel), rank_rational_mem p (0 / 1 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C3T29.kc = {0} := rfl
      have hd' : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C3T29_reduced_loads_nonzero p hp).2 0 hd
      rw [C3T29_cload_0]
      exact ⟨rank_rational_mem p (1 / 1 : ℚ) hp (by decide +kernel), rank_rational_mem p (0 / 1 : ℚ) hp (by decide +kernel), by simpa only [C3T29_cload_0] using hn⟩
  · refine ⟨C3T32_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T32.kr = {0} := rfl
      have hd' : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C3T32_rload_0]
      exact ⟨rank_rational_mem p (1 / 1 : ℚ) hp (by decide +kernel), rank_rational_mem p (0 / 1 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C3T32.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T33_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T33.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T33.kc = {0} := rfl
      have hd' : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C3T33_reduced_loads_nonzero p hp).2 0 hd
      rw [C3T33_cload_0]
      exact ⟨rank_rational_mem p (1 / 1 : ℚ) hp (by decide +kernel), rank_rational_mem p (0 / 1 : ℚ) hp (by decide +kernel), by simpa only [C3T33_cload_0] using hn⟩
  · refine ⟨C3T30_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T30.kr = {0} := rfl
      have hd' : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C3T30_rload_0]
      exact ⟨rank_rational_mem p (1 / 1 : ℚ) hp (by decide +kernel), rank_rational_mem p (-4 / 3 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C3T30.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T31_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T31.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T31.kc = {0} := rfl
      have hd' : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C3T31_reduced_loads_nonzero p hp).2 0 hd
      rw [C3T31_cload_0]
      exact ⟨rank_rational_mem p (1 / 1 : ℚ) hp (by decide +kernel), rank_rational_mem p (-4 / 3 : ℚ) hp (by decide +kernel), by simpa only [C3T31_cload_0] using hn⟩
  · simp [trivCert, FibreCert.triv]

#print axioms C3S19_load_facts
end CatalanCore.Uniform.Bank.Lambda.RankFacts
