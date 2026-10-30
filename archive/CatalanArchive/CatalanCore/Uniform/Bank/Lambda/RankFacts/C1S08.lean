import CatalanCore.Uniform.Bank.Lambda.RankFibre.C1S08
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T11
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T12
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T14
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T15
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T16
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T17
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T18
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankFacts
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
open RankFibre RankData RankLoads
open scoped Classical

theorem C1S08_load_facts (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hp : rankPrimeCutoff < p) (x : ZMod p) :
    let c := C1S08_assignment a p r m s ha hp29 hp4 hrp hm1 x
    (c.kr.card ≤ 1 ∧ c.kc.card ≤ 1) ∧
    (∀ d ∈ c.kr, (c.rload d).1 ∈ S p ∧ (c.rload d).2 ∈ S p) ∧
    (∀ d ∈ c.kc, (c.cload d).1 ∈ S p ∧ (c.cload d).2 ∈ S p ∧ castV p (c.cload d) ≠ 0) := by
  dsimp only
  unfold C1S08_assignment
  split_ifs
  · refine ⟨C1T15_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T15.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T15.kc = {3} := rfl
      have hd' : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C1T15_reduced_loads_nonzero p hp).2 3 hd
      rw [C1T15_cload_3]
      exact ⟨rank_rational_mem p (-1397921 / 1458540 : ℚ) hp (by decide +kernel), rank_rational_mem p (-2931619 / 1458540 : ℚ) hp (by decide +kernel), by simpa only [C1T15_cload_3] using hn⟩
  · refine ⟨C1T16_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T16.kr = {3} := rfl
      have hd' : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C1T16_rload_3]
      exact ⟨rank_rational_mem p (-1397921 / 1458540 : ℚ) hp (by decide +kernel), rank_rational_mem p (-2931619 / 1458540 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C1T16.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T11_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T11.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T11.kc = {3} := rfl
      have hd' : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C1T11_reduced_loads_nonzero p hp).2 3 hd
      rw [C1T11_cload_3]
      exact ⟨rank_rational_mem p (2439392450783 / 2463829399980 : ℚ) hp (by decide +kernel), rank_rational_mem p (-9066989195663 / 2463829399980 : ℚ) hp (by decide +kernel), by simpa only [C1T11_cload_3] using hn⟩
  · refine ⟨C1T12_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T12.kr = {3} := rfl
      have hd' : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C1T12_rload_3]
      exact ⟨rank_rational_mem p (2439392450783 / 2463829399980 : ℚ) hp (by decide +kernel), rank_rational_mem p (-9066989195663 / 2463829399980 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C1T12.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T14_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T14.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T14.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T14_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T14.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T14.kc = ∅ := rfl
      simp [he] at hd
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
  · simp [trivCert, FibreCert.triv]

#print axioms C1S08_load_facts
end CatalanCore.Uniform.Bank.Lambda.RankFacts
