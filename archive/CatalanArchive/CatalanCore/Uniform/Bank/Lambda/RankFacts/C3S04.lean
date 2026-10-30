import CatalanCore.Uniform.Bank.Lambda.RankFibre.C3S04
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T05
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T06
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T08
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T09
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T10
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T11
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T12
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankFacts
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
open RankFibre RankData RankLoads
open scoped Classical

theorem C3S04_load_facts (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hp : rankPrimeCutoff < p) (x : ZMod p) :
    let c := C3S04_assignment a p r m s ha hp29 hp4 hrp hm1 x
    (c.kr.card ≤ 1 ∧ c.kc.card ≤ 1) ∧
    (∀ d ∈ c.kr, (c.rload d).1 ∈ S p ∧ (c.rload d).2 ∈ S p) ∧
    (∀ d ∈ c.kc, (c.cload d).1 ∈ S p ∧ (c.cload d).2 ∈ S p ∧ castV p (c.cload d) ≠ 0) := by
  dsimp only
  unfold C3S04_assignment
  split_ifs
  · refine ⟨C3T08_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T08.kr = {4} := rfl
      have hd' : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C3T08_rload_4]
      exact ⟨rank_rational_mem p (-15734175008 / 581539134407 : ℚ) hp (by decide +kernel), rank_rational_mem p (-6619969800313 / 23261565376280 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C3T08.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T09_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T09.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T09.kc = {4} := rfl
      have hd' : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C3T09_reduced_loads_nonzero p hp).2 4 hd
      rw [C3T09_cload_4]
      exact ⟨rank_rational_mem p (-15734175008 / 581539134407 : ℚ) hp (by decide +kernel), rank_rational_mem p (-6619969800313 / 23261565376280 : ℚ) hp (by decide +kernel), by simpa only [C3T09_cload_4] using hn⟩
  · refine ⟨C3T05_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T05.kr = {4} := rfl
      have hd' : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C3T05_rload_4]
      exact ⟨rank_rational_mem p (75604259621642373344 / 89994173950490079655 : ℚ) hp (by decide +kernel), rank_rational_mem p (-6423714826532779939 / 13090061665525829768 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C3T05.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T06_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T06.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T06.kc = {4} := rfl
      have hd' : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C3T06_reduced_loads_nonzero p hp).2 4 hd
      rw [C3T06_cload_4]
      exact ⟨rank_rational_mem p (75604259621642373344 / 89994173950490079655 : ℚ) hp (by decide +kernel), rank_rational_mem p (-6423714826532779939 / 13090061665525829768 : ℚ) hp (by decide +kernel), by simpa only [C3T06_cload_4] using hn⟩
  · refine ⟨C3T10_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T10.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T10.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T10_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T10.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T10.kc = ∅ := rfl
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
  · simp [trivCert, FibreCert.triv]

#print axioms C3S04_load_facts
end CatalanCore.Uniform.Bank.Lambda.RankFacts
