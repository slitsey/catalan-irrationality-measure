import CatalanCore.Uniform.Bank.Sevenths.RankFibre.C1S00
import CatalanCore.Uniform.Bank.Sevenths.RankLoads.C1
import CatalanCore.Uniform.Bank.Sevenths.RankLoads.C1
import CatalanCore.Uniform.Bank.Sevenths.RankLoads.C1
import CatalanCore.Uniform.Bank.Sevenths.RankLoads.C1
import CatalanCore.Uniform.Bank.Sevenths.RankLoads.C1
import CatalanCore.Uniform.Bank.Sevenths.RankLoads.C1
import CatalanCore.Uniform.Bank.Sevenths.RankLoads.C1
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankFacts
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
open RankFibre RankData RankLoads
open CatalanCore.Uniform.Content.RankProducer.Geometry
open scoped Classical

theorem C1S00_load_facts (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : 1 ≤ a ∧ a ≤ 6) (hp64 : 64 ≤ p) (hp7 : ¬ p ∣ 7)
    (hrp : r ≤ 6 * p) (hm1 : 12 * m ≤ r + 6) (hp : rankPrimeCutoff < p) (x : ZMod p) :
    let c := C1S00_assignment a p r m s ha hp64 hp7 hrp hm1 x
    (c.kr.card ≤ 1 ∧ c.kc.card ≤ 1) ∧
    (∀ d ∈ c.kr, (c.rload d).1 ∈ S p ∧ (c.rload d).2 ∈ S p) ∧
    (∀ d ∈ c.kc, (c.cload d).1 ∈ S p ∧ (c.cload d).2 ∈ S p ∧ castV p (c.cload d) ≠ 0) := by
  dsimp only
  unfold C1S00_assignment
  split_ifs
  · refine ⟨C1T00_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T00.kr = {6} := rfl
      have hd' : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C1T00_rload_6]
      exact ⟨rank_rational_mem p (-1427790115970909280998634104325747868808 / 5454674359830046949033009432616846411125 : ℚ) hp (by decide +kernel), rank_rational_mem p (-1902208755681645118418120850728652548272049 / 392736553907763380330376679148412941601000 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C1T00.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T01_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T01.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T01.kc = {6} := rfl
      have hd' : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C1T01_reduced_loads_nonzero p hp).2 6 hd
      rw [C1T01_cload_6]
      exact ⟨rank_rational_mem p (-1427790115970909280998634104325747868808 / 5454674359830046949033009432616846411125 : ℚ) hp (by decide +kernel), rank_rational_mem p (-1902208755681645118418120850728652548272049 / 392736553907763380330376679148412941601000 : ℚ) hp (by decide +kernel), by simpa only [C1T01_cload_6] using hn⟩
  · refine ⟨C1T02_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T02.kr = {6} := rfl
      have hd' : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C1T02_rload_6]
      exact ⟨rank_rational_mem p (4636750447571997559221060361775872780732963408494446 / 4643193594935921891088267681836784305796698716941375 : ℚ) hp (by decide +kernel), rank_rational_mem p (-757642551055354749996506551595817222881370572249524909 / 111436646278462125386118424364082823339120769206593000 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C1T02.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T03_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T03.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T03.kc = {6} := rfl
      have hd' : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C1T03_reduced_loads_nonzero p hp).2 6 hd
      rw [C1T03_cload_6]
      exact ⟨rank_rational_mem p (4636750447571997559221060361775872780732963408494446 / 4643193594935921891088267681836784305796698716941375 : ℚ) hp (by decide +kernel), rank_rational_mem p (-757642551055354749996506551595817222881370572249524909 / 111436646278462125386118424364082823339120769206593000 : ℚ) hp (by decide +kernel), by simpa only [C1T03_cload_6] using hn⟩
  · refine ⟨C1T04_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T04.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T04.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T04_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T04.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T04.kc = ∅ := rfl
      simp [he] at hd
  · refine ⟨C1T05_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T05.kr = ∅ := rfl
      simp [he] at hd
    · intro d hd
      have he : C1T05.kc = {5} := rfl
      have hd' : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      have hn := (C1T05_reduced_loads_nonzero p hp).2 5 hd
      rw [C1T05_cload_5]
      exact ⟨rank_rational_mem p (161095237687746216896798069934142109 / 161343721758715873364292979985985795 : ℚ) hp (by decide +kernel), rank_rational_mem p (-14632101432614264961069085104418237891 / 2151249623449544978190573066479810600 : ℚ) hp (by decide +kernel), by simpa only [C1T05_cload_5] using hn⟩
  · refine ⟨C1T06_small_kills, ?_, ?_⟩
    · intro d hd
      have he : C1T06.kr = {5} := rfl
      have hd' : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
      subst d
      rw [C1T06_rload_5]
      exact ⟨rank_rational_mem p (161095237687746216896798069934142109 / 161343721758715873364292979985985795 : ℚ) hp (by decide +kernel), rank_rational_mem p (-14632101432614264961069085104418237891 / 2151249623449544978190573066479810600 : ℚ) hp (by decide +kernel)⟩
    · intro d hd
      have he : C1T06.kc = ∅ := rfl
      simp [he] at hd
  · simp [trivCert, FibreCert.triv]

#print axioms C1S00_load_facts
end CatalanCore.Uniform.Bank.Sevenths.RankFacts
