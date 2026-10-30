import CatalanCore.Uniform.Bank.Lambda.RankFibre.C3S00
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T00
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T01
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T02
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T03
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T04
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T05
import CatalanCore.Uniform.Bank.Lambda.RankLoads.C3T06
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda.RankFacts
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
open RankFibre RankData RankLoads
open scoped Classical

theorem C3S00_load_facts (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (hp : rankPrimeCutoff < p) (x : ZMod p) :
    let c := C3S00_assignment a p r m s ha hp29 hp4 hrp hm1 x
    (c.kr.card ≤ 1 ∧ c.kc.card ≤ 1) ∧
    (∀ d ∈ c.kr, (c.rload d).1 ∈ S p ∧ (c.rload d).2 ∈ S p) ∧
    (∀ d ∈ c.kc, (c.cload d).1 ∈ S p ∧ (c.cload d).2 ∈ S p ∧ castV p (c.cload d) ≠ 0) := by
  dsimp only
  unfold C3S00_assignment
  split_ifs
  · refine ⟨C3T00_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T00.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T00.kc = {5} := rfl
      have hd' : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C3T00_reduced_loads_nonzero p hp).2 5 hd
      rw [C3T00_cload_5]
      exact ⟨rank_rational_mem p (58040617587411647653 / 360543338619249332525 : ℚ) hp (by decide +kernel), rank_rational_mem p (-6247154238882597275657 / 20190426962677962621400 : ℚ) hp (by decide +kernel), by simpa only [C3T00_cload_5] using hn⟩
  · refine ⟨C3T01_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T01.kr = {5} := rfl
      have hd' : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C3T01_rload_5]
      exact ⟨rank_rational_mem p (58040617587411647653 / 360543338619249332525 : ℚ) hp (by decide +kernel), rank_rational_mem p (-6247154238882597275657 / 20190426962677962621400 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C3T01.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T02_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T02.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T02.kc = {5} := rfl
      have hd' : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C3T02_reduced_loads_nonzero p hp).2 5 hd
      rw [C3T02_cload_5]
      exact ⟨rank_rational_mem p (27646144566798850106926380584243 / 32252203580227729735959115607275 : ℚ) hp (by decide +kernel), rank_rational_mem p (-125867971596035968488506433994681 / 258017628641821837887672924858200 : ℚ) hp (by decide +kernel), by simpa only [C3T02_cload_5] using hn⟩
  · refine ⟨C3T03_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T03.kr = {5} := rfl
      have hd' : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C3T03_rload_5]
      exact ⟨rank_rational_mem p (27646144566798850106926380584243 / 32252203580227729735959115607275 : ℚ) hp (by decide +kernel), rank_rational_mem p (-125867971596035968488506433994681 / 258017628641821837887672924858200 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C3T03.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T04_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T04.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T04.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C3T04_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C3T04.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C3T04.kc = ∅ := rfl
      simp [he] at hd
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
  · simp [trivCert, FibreCert.triv]

#print axioms C3S00_load_facts
end CatalanCore.Uniform.Bank.Lambda.RankFacts
