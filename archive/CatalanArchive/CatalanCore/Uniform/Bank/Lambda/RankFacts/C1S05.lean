import CatalanCore.Uniform.Bank.Lambda.RankFibre.C1S05
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T08
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T09
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T10
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T11
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T12
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C1T13
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankFacts
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
open RankFibre RankData RankLoads
open scoped Classical

theorem C1S05_load_facts (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hp : rankPrimeCutoff < p) (x : ZMod p) :
    let c := C1S05_assignment a p r m s ha hp29 hp4 hrp hm1 x
    (c.kr.card ≤ 1 ∧ c.kc.card ≤ 1) ∧
    (∀ d ∈ c.kr, (c.rload d).1 ∈ S p ∧ (c.rload d).2 ∈ S p) ∧
    (∀ d ∈ c.kc, (c.cload d).1 ∈ S p ∧ (c.cload d).2 ∈ S p ∧ castV p (c.cload d) ≠ 0) := by
  dsimp only
  unfold C1S05_assignment
  split_ifs
  · refine ⟨C1T08_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T08.kr = {4} := rfl
      have hd' : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C1T08_rload_4]
      exact ⟨rank_rational_mem p (-1923630295976 / 4570623985005 : ℚ) hp (by decide +kernel), rank_rational_mem p (-257538007361335 / 114570307890792 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C1T08.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T09_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T09.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T09.kc = {4} := rfl
      have hd' : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C1T09_reduced_loads_nonzero p hp).2 4 hd
      rw [C1T09_cload_4]
      exact ⟨rank_rational_mem p (-1923630295976 / 4570623985005 : ℚ) hp (by decide +kernel), rank_rational_mem p (-257538007361335 / 114570307890792 : ℚ) hp (by decide +kernel), by simpa only [C1T09_cload_4] using hn⟩
  · refine ⟨C1T13_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T13.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T13.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T13_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T13.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T13.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T10_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T10.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T10.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T10_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T10.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T10.kc = ∅ := rfl
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
  · simp [trivCert, FibreCert.triv]

#print axioms C1S05_load_facts
end CatalanCore.Uniform.Bank.Lambda.RankFacts
