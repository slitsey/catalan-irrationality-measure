import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C1
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData
theorem C1T00_small_kills : C1T00.kr.card ≤ 1 ∧ C1T00.kc.card ≤ 1 := by decide +kernel

theorem C1T00_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T00.Integral p := by
  apply C1T00_integral p
  intro hd
  have hpos : 0 < C1T00_den := by decide +kernel
  have hbound : C1T00_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T00_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T00.kr, castV p (C1T00.rload d) ≠ 0) ∧
    (∀ d ∈ C1T00.kc, castV p (C1T00.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T00.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T00_rload_6]
    exact rank_castV_ne_zero_of_fst p ((-1427790115970909280998634104325747868808 / 5454674359830046949033009432616846411125), (-1902208755681645118418120850728652548272049 / 392736553907763380330376679148412941601000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T00.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T00_large_integral
#print axioms C1T00_reduced_loads_nonzero

theorem C1T01_small_kills : C1T01.kr.card ≤ 1 ∧ C1T01.kc.card ≤ 1 := by decide +kernel

theorem C1T01_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T01.Integral p := by
  apply C1T01_integral p
  intro hd
  have hpos : 0 < C1T01_den := by decide +kernel
  have hbound : C1T01_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T01_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T01.kr, castV p (C1T01.rload d) ≠ 0) ∧
    (∀ d ∈ C1T01.kc, castV p (C1T01.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T01.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T01.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T01_cload_6]
    exact rank_castV_ne_zero_of_fst p ((-1427790115970909280998634104325747868808 / 5454674359830046949033009432616846411125), (-1902208755681645118418120850728652548272049 / 392736553907763380330376679148412941601000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T01_large_integral
#print axioms C1T01_reduced_loads_nonzero

theorem C1T02_small_kills : C1T02.kr.card ≤ 1 ∧ C1T02.kc.card ≤ 1 := by decide +kernel

theorem C1T02_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T02.Integral p := by
  apply C1T02_integral p
  intro hd
  have hpos : 0 < C1T02_den := by decide +kernel
  have hbound : C1T02_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T02_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T02.kr, castV p (C1T02.rload d) ≠ 0) ∧
    (∀ d ∈ C1T02.kc, castV p (C1T02.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T02.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T02_rload_6]
    exact rank_castV_ne_zero_of_fst p ((4636750447571997559221060361775872780732963408494446 / 4643193594935921891088267681836784305796698716941375), (-757642551055354749996506551595817222881370572249524909 / 111436646278462125386118424364082823339120769206593000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T02.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T02_large_integral
#print axioms C1T02_reduced_loads_nonzero

theorem C1T03_small_kills : C1T03.kr.card ≤ 1 ∧ C1T03.kc.card ≤ 1 := by decide +kernel

theorem C1T03_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T03.Integral p := by
  apply C1T03_integral p
  intro hd
  have hpos : 0 < C1T03_den := by decide +kernel
  have hbound : C1T03_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T03_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T03.kr, castV p (C1T03.rload d) ≠ 0) ∧
    (∀ d ∈ C1T03.kc, castV p (C1T03.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T03.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T03.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T03_cload_6]
    exact rank_castV_ne_zero_of_fst p ((4636750447571997559221060361775872780732963408494446 / 4643193594935921891088267681836784305796698716941375), (-757642551055354749996506551595817222881370572249524909 / 111436646278462125386118424364082823339120769206593000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T03_large_integral
#print axioms C1T03_reduced_loads_nonzero

theorem C1T04_small_kills : C1T04.kr.card ≤ 1 ∧ C1T04.kc.card ≤ 1 := by decide +kernel

theorem C1T04_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T04.Integral p := by
  apply C1T04_integral p
  intro hd
  have hpos : 0 < C1T04_den := by decide +kernel
  have hbound : C1T04_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T04_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T04.kr, castV p (C1T04.rload d) ≠ 0) ∧
    (∀ d ∈ C1T04.kc, castV p (C1T04.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T04.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T04.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T04_large_integral
#print axioms C1T04_reduced_loads_nonzero

theorem C1T05_small_kills : C1T05.kr.card ≤ 1 ∧ C1T05.kc.card ≤ 1 := by decide +kernel

theorem C1T05_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T05.Integral p := by
  apply C1T05_integral p
  intro hd
  have hpos : 0 < C1T05_den := by decide +kernel
  have hbound : C1T05_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T05_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T05.kr, castV p (C1T05.rload d) ≠ 0) ∧
    (∀ d ∈ C1T05.kc, castV p (C1T05.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T05.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T05.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T05_cload_5]
    exact rank_castV_ne_zero_of_fst p ((161095237687746216896798069934142109 / 161343721758715873364292979985985795), (-14632101432614264961069085104418237891 / 2151249623449544978190573066479810600)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T05_large_integral
#print axioms C1T05_reduced_loads_nonzero

theorem C1T06_small_kills : C1T06.kr.card ≤ 1 ∧ C1T06.kc.card ≤ 1 := by decide +kernel

theorem C1T06_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T06.Integral p := by
  apply C1T06_integral p
  intro hd
  have hpos : 0 < C1T06_den := by decide +kernel
  have hbound : C1T06_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T06_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T06.kr, castV p (C1T06.rload d) ≠ 0) ∧
    (∀ d ∈ C1T06.kc, castV p (C1T06.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T06.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T06_rload_5]
    exact rank_castV_ne_zero_of_fst p ((161095237687746216896798069934142109 / 161343721758715873364292979985985795), (-14632101432614264961069085104418237891 / 2151249623449544978190573066479810600)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T06.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T06_large_integral
#print axioms C1T06_reduced_loads_nonzero

theorem C1T07_small_kills : C1T07.kr.card ≤ 1 ∧ C1T07.kc.card ≤ 1 := by decide +kernel

theorem C1T07_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T07.Integral p := by
  apply C1T07_integral p
  intro hd
  have hpos : 0 < C1T07_den := by decide +kernel
  have hbound : C1T07_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T07_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T07.kr, castV p (C1T07.rload d) ≠ 0) ∧
    (∀ d ∈ C1T07.kc, castV p (C1T07.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T07.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T07.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T07_large_integral
#print axioms C1T07_reduced_loads_nonzero

theorem C1T08_small_kills : C1T08.kr.card ≤ 1 ∧ C1T08.kc.card ≤ 1 := by decide +kernel

theorem C1T08_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T08.Integral p := by
  apply C1T08_integral p
  intro hd
  have hpos : 0 < C1T08_den := by decide +kernel
  have hbound : C1T08_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T08_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T08.kr, castV p (C1T08.rload d) ≠ 0) ∧
    (∀ d ∈ C1T08.kc, castV p (C1T08.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T08.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T08.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T08_cload_5]
    exact rank_castV_ne_zero_of_fst p ((-620872194061560215917994033 / 1183934788022501064083853000), (-3638866639296810540691286813 / 789289858681667376055902000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T08_large_integral
#print axioms C1T08_reduced_loads_nonzero

theorem C1T09_small_kills : C1T09.kr.card ≤ 1 ∧ C1T09.kc.card ≤ 1 := by decide +kernel

theorem C1T09_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T09.Integral p := by
  apply C1T09_integral p
  intro hd
  have hpos : 0 < C1T09_den := by decide +kernel
  have hbound : C1T09_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T09_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T09.kr, castV p (C1T09.rload d) ≠ 0) ∧
    (∀ d ∈ C1T09.kc, castV p (C1T09.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T09.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T09_rload_5]
    exact rank_castV_ne_zero_of_fst p ((-620872194061560215917994033 / 1183934788022501064083853000), (-3638866639296810540691286813 / 789289858681667376055902000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T09.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T09_large_integral
#print axioms C1T09_reduced_loads_nonzero

theorem C1T10_small_kills : C1T10.kr.card ≤ 1 ∧ C1T10.kc.card ≤ 1 := by decide +kernel

theorem C1T10_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T10.Integral p := by
  apply C1T10_integral p
  intro hd
  have hpos : 0 < C1T10_den := by decide +kernel
  have hbound : C1T10_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T10_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T10.kr, castV p (C1T10.rload d) ≠ 0) ∧
    (∀ d ∈ C1T10.kc, castV p (C1T10.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T10.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T10.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T10_large_integral
#print axioms C1T10_reduced_loads_nonzero

theorem C1T11_small_kills : C1T11.kr.card ≤ 1 ∧ C1T11.kc.card ≤ 1 := by decide +kernel

theorem C1T11_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T11.Integral p := by
  apply C1T11_integral p
  intro hd
  have hpos : 0 < C1T11_den := by decide +kernel
  have hbound : C1T11_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T11_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T11.kr, castV p (C1T11.rload d) ≠ 0) ∧
    (∀ d ∈ C1T11.kc, castV p (C1T11.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T11.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T11_rload_4]
    exact rank_castV_ne_zero_of_fst p ((7520266191241547495046271 / 7533320441904572009947560), (-34180591495347838975550029 / 5022213627936381339965040)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T11.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T11_large_integral
#print axioms C1T11_reduced_loads_nonzero

theorem C1T12_small_kills : C1T12.kr.card ≤ 1 ∧ C1T12.kc.card ≤ 1 := by decide +kernel

theorem C1T12_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T12.Integral p := by
  apply C1T12_integral p
  intro hd
  have hpos : 0 < C1T12_den := by decide +kernel
  have hbound : C1T12_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T12_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T12.kr, castV p (C1T12.rload d) ≠ 0) ∧
    (∀ d ∈ C1T12.kc, castV p (C1T12.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T12.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T12.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T12_cload_4]
    exact rank_castV_ne_zero_of_fst p ((7520266191241547495046271 / 7533320441904572009947560), (-34180591495347838975550029 / 5022213627936381339965040)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T12_large_integral
#print axioms C1T12_reduced_loads_nonzero

theorem C1T13_small_kills : C1T13.kr.card ≤ 1 ∧ C1T13.kc.card ≤ 1 := by decide +kernel

theorem C1T13_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T13.Integral p := by
  apply C1T13_integral p
  intro hd
  have hpos : 0 < C1T13_den := by decide +kernel
  have hbound : C1T13_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T13_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T13.kr, castV p (C1T13.rload d) ≠ 0) ∧
    (∀ d ∈ C1T13.kc, castV p (C1T13.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T13.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T13.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T13_large_integral
#print axioms C1T13_reduced_loads_nonzero

theorem C1T14_small_kills : C1T14.kr.card ≤ 1 ∧ C1T14.kc.card ≤ 1 := by decide +kernel

theorem C1T14_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T14.Integral p := by
  apply C1T14_integral p
  intro hd
  have hpos : 0 < C1T14_den := by decide +kernel
  have hbound : C1T14_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T14_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T14.kr, castV p (C1T14.rload d) ≠ 0) ∧
    (∀ d ∈ C1T14.kc, castV p (C1T14.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T14.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T14.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T14_large_integral
#print axioms C1T14_reduced_loads_nonzero

theorem C1T15_small_kills : C1T15.kr.card ≤ 1 ∧ C1T15.kc.card ≤ 1 := by decide +kernel

theorem C1T15_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T15.Integral p := by
  apply C1T15_integral p
  intro hd
  have hpos : 0 < C1T15_den := by decide +kernel
  have hbound : C1T15_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T15_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T15.kr, castV p (C1T15.rload d) ≠ 0) ∧
    (∀ d ∈ C1T15.kc, castV p (C1T15.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T15.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T15_rload_4]
    exact rank_castV_ne_zero_of_fst p ((-796007066211827 / 845782648686360), (-2424410564966207 / 563855099124240)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T15.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T15_large_integral
#print axioms C1T15_reduced_loads_nonzero

theorem C1T16_small_kills : C1T16.kr.card ≤ 1 ∧ C1T16.kc.card ≤ 1 := by decide +kernel

theorem C1T16_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T16.Integral p := by
  apply C1T16_integral p
  intro hd
  have hpos : 0 < C1T16_den := by decide +kernel
  have hbound : C1T16_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T16_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T16.kr, castV p (C1T16.rload d) ≠ 0) ∧
    (∀ d ∈ C1T16.kc, castV p (C1T16.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T16.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T16.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T16_cload_4]
    exact rank_castV_ne_zero_of_fst p ((-796007066211827 / 845782648686360), (-2424410564966207 / 563855099124240)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T16_large_integral
#print axioms C1T16_reduced_loads_nonzero

theorem C1T17_small_kills : C1T17.kr.card ≤ 1 ∧ C1T17.kc.card ≤ 1 := by decide +kernel

theorem C1T17_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T17.Integral p := by
  apply C1T17_integral p
  intro hd
  have hpos : 0 < C1T17_den := by decide +kernel
  have hbound : C1T17_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T17_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T17.kr, castV p (C1T17.rload d) ≠ 0) ∧
    (∀ d ∈ C1T17.kc, castV p (C1T17.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T17.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T17.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T17_cload_3]
    exact rank_castV_ne_zero_of_fst p ((47126631993233 / 47220172986690), (-1286798649003677 / 188880691946760)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T17_large_integral
#print axioms C1T17_reduced_loads_nonzero

theorem C1T18_small_kills : C1T18.kr.card ≤ 1 ∧ C1T18.kc.card ≤ 1 := by decide +kernel

theorem C1T18_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T18.Integral p := by
  apply C1T18_integral p
  intro hd
  have hpos : 0 < C1T18_den := by decide +kernel
  have hbound : C1T18_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T18_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T18.kr, castV p (C1T18.rload d) ≠ 0) ∧
    (∀ d ∈ C1T18.kc, castV p (C1T18.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T18.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T18_rload_3]
    exact rank_castV_ne_zero_of_fst p ((47126631993233 / 47220172986690), (-1286798649003677 / 188880691946760)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T18.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T18_large_integral
#print axioms C1T18_reduced_loads_nonzero

theorem C1T19_small_kills : C1T19.kr.card ≤ 1 ∧ C1T19.kc.card ≤ 1 := by decide +kernel

theorem C1T19_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T19.Integral p := by
  apply C1T19_integral p
  intro hd
  have hpos : 0 < C1T19_den := by decide +kernel
  have hbound : C1T19_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T19_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T19.kr, castV p (C1T19.rload d) ≠ 0) ∧
    (∀ d ∈ C1T19.kc, castV p (C1T19.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T19.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T19.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T19_large_integral
#print axioms C1T19_reduced_loads_nonzero

theorem C1T20_small_kills : C1T20.kr.card ≤ 1 ∧ C1T20.kc.card ≤ 1 := by decide +kernel

theorem C1T20_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T20.Integral p := by
  apply C1T20_integral p
  intro hd
  have hpos : 0 < C1T20_den := by decide +kernel
  have hbound : C1T20_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T20_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T20.kr, castV p (C1T20.rload d) ≠ 0) ∧
    (∀ d ∈ C1T20.kc, castV p (C1T20.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T20.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T20.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T20_large_integral
#print axioms C1T20_reduced_loads_nonzero

theorem C1T21_small_kills : C1T21.kr.card ≤ 1 ∧ C1T21.kc.card ≤ 1 := by decide +kernel

theorem C1T21_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T21.Integral p := by
  apply C1T21_integral p
  intro hd
  have hpos : 0 < C1T21_den := by decide +kernel
  have hbound : C1T21_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T21_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T21.kr, castV p (C1T21.rload d) ≠ 0) ∧
    (∀ d ∈ C1T21.kc, castV p (C1T21.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T21.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T21.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T21_cload_3]
    exact rank_castV_ne_zero_of_fst p ((-25769 / 14976), (-1185469 / 307008)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T21_large_integral
#print axioms C1T21_reduced_loads_nonzero

theorem C1T22_small_kills : C1T22.kr.card ≤ 1 ∧ C1T22.kc.card ≤ 1 := by decide +kernel

theorem C1T22_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T22.Integral p := by
  apply C1T22_integral p
  intro hd
  have hpos : 0 < C1T22_den := by decide +kernel
  have hbound : C1T22_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T22_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T22.kr, castV p (C1T22.rload d) ≠ 0) ∧
    (∀ d ∈ C1T22.kc, castV p (C1T22.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T22.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T22_rload_3]
    exact rank_castV_ne_zero_of_fst p ((-25769 / 14976), (-1185469 / 307008)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T22.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T22_large_integral
#print axioms C1T22_reduced_loads_nonzero

theorem C1T23_small_kills : C1T23.kr.card ≤ 1 ∧ C1T23.kc.card ≤ 1 := by decide +kernel

theorem C1T23_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T23.Integral p := by
  apply C1T23_integral p
  intro hd
  have hpos : 0 < C1T23_den := by decide +kernel
  have hbound : C1T23_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T23_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T23.kr, castV p (C1T23.rload d) ≠ 0) ∧
    (∀ d ∈ C1T23.kc, castV p (C1T23.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T23.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T23_rload_2]
    exact rank_castV_ne_zero_of_fst p ((12206183 / 12234240), (-869867 / 127440)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T23.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T23_large_integral
#print axioms C1T23_reduced_loads_nonzero

theorem C1T24_small_kills : C1T24.kr.card ≤ 1 ∧ C1T24.kc.card ≤ 1 := by decide +kernel

theorem C1T24_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T24.Integral p := by
  apply C1T24_integral p
  intro hd
  have hpos : 0 < C1T24_den := by decide +kernel
  have hbound : C1T24_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T24_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T24.kr, castV p (C1T24.rload d) ≠ 0) ∧
    (∀ d ∈ C1T24.kc, castV p (C1T24.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T24.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T24.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T24_cload_2]
    exact rank_castV_ne_zero_of_fst p ((12206183 / 12234240), (-869867 / 127440)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T24_large_integral
#print axioms C1T24_reduced_loads_nonzero

theorem C1T25_small_kills : C1T25.kr.card ≤ 1 ∧ C1T25.kc.card ≤ 1 := by decide +kernel

theorem C1T25_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T25.Integral p := by
  apply C1T25_integral p
  intro hd
  have hpos : 0 < C1T25_den := by decide +kernel
  have hbound : C1T25_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T25_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T25.kr, castV p (C1T25.rload d) ≠ 0) ∧
    (∀ d ∈ C1T25.kc, castV p (C1T25.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T25.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T25.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T25_large_integral
#print axioms C1T25_reduced_loads_nonzero

theorem C1T26_small_kills : C1T26.kr.card ≤ 1 ∧ C1T26.kc.card ≤ 1 := by decide +kernel

theorem C1T26_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T26.Integral p := by
  apply C1T26_integral p
  intro hd
  have hpos : 0 < C1T26_den := by decide +kernel
  have hbound : C1T26_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T26_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T26.kr, castV p (C1T26.rload d) ≠ 0) ∧
    (∀ d ∈ C1T26.kc, castV p (C1T26.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T26.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T26.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T26_large_integral
#print axioms C1T26_reduced_loads_nonzero

theorem C1T27_small_kills : C1T27.kr.card ≤ 1 ∧ C1T27.kc.card ≤ 1 := by decide +kernel

theorem C1T27_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T27.Integral p := by
  apply C1T27_integral p
  intro hd
  have hpos : 0 < C1T27_den := by decide +kernel
  have hbound : C1T27_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T27_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T27.kr, castV p (C1T27.rload d) ≠ 0) ∧
    (∀ d ∈ C1T27.kc, castV p (C1T27.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T27.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T27_rload_2]
    exact rank_castV_ne_zero_of_fst p ((-123 / 32), (-51 / 16)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T27.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T27_large_integral
#print axioms C1T27_reduced_loads_nonzero

theorem C1T28_small_kills : C1T28.kr.card ≤ 1 ∧ C1T28.kc.card ≤ 1 := by decide +kernel

theorem C1T28_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T28.Integral p := by
  apply C1T28_integral p
  intro hd
  have hpos : 0 < C1T28_den := by decide +kernel
  have hbound : C1T28_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T28_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T28.kr, castV p (C1T28.rload d) ≠ 0) ∧
    (∀ d ∈ C1T28.kc, castV p (C1T28.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T28.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T28.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T28_cload_2]
    exact rank_castV_ne_zero_of_fst p ((-123 / 32), (-51 / 16)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T28_large_integral
#print axioms C1T28_reduced_loads_nonzero

theorem C1T29_small_kills : C1T29.kr.card ≤ 1 ∧ C1T29.kc.card ≤ 1 := by decide +kernel

theorem C1T29_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T29.Integral p := by
  apply C1T29_integral p
  intro hd
  have hpos : 0 < C1T29_den := by decide +kernel
  have hbound : C1T29_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T29_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T29.kr, castV p (C1T29.rload d) ≠ 0) ∧
    (∀ d ∈ C1T29.kc, castV p (C1T29.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T29.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T29.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T29_cload_1]
    exact rank_castV_ne_zero_of_fst p ((391 / 392), (-48 / 7)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T29_large_integral
#print axioms C1T29_reduced_loads_nonzero

theorem C1T30_small_kills : C1T30.kr.card ≤ 1 ∧ C1T30.kc.card ≤ 1 := by decide +kernel

theorem C1T30_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T30.Integral p := by
  apply C1T30_integral p
  intro hd
  have hpos : 0 < C1T30_den := by decide +kernel
  have hbound : C1T30_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T30_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T30.kr, castV p (C1T30.rload d) ≠ 0) ∧
    (∀ d ∈ C1T30.kc, castV p (C1T30.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T30.kr = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T30_rload_1]
    exact rank_castV_ne_zero_of_fst p ((391 / 392), (-48 / 7)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T30.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T30_large_integral
#print axioms C1T30_reduced_loads_nonzero

theorem C1T31_small_kills : C1T31.kr.card ≤ 1 ∧ C1T31.kc.card ≤ 1 := by decide +kernel

theorem C1T31_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T31.Integral p := by
  apply C1T31_integral p
  intro hd
  have hpos : 0 < C1T31_den := by decide +kernel
  have hbound : C1T31_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T31_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T31.kr, castV p (C1T31.rload d) ≠ 0) ∧
    (∀ d ∈ C1T31.kc, castV p (C1T31.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T31.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T31.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T31_large_integral
#print axioms C1T31_reduced_loads_nonzero

theorem C1T32_small_kills : C1T32.kr.card ≤ 1 ∧ C1T32.kc.card ≤ 1 := by decide +kernel

theorem C1T32_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T32.Integral p := by
  apply C1T32_integral p
  intro hd
  have hpos : 0 < C1T32_den := by decide +kernel
  have hbound : C1T32_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T32_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T32.kr, castV p (C1T32.rload d) ≠ 0) ∧
    (∀ d ∈ C1T32.kc, castV p (C1T32.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T32.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T32.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T32_large_integral
#print axioms C1T32_reduced_loads_nonzero

theorem C1T33_small_kills : C1T33.kr.card ≤ 1 ∧ C1T33.kc.card ≤ 1 := by decide +kernel

theorem C1T33_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T33.Integral p := by
  apply C1T33_integral p
  intro hd
  have hpos : 0 < C1T33_den := by decide +kernel
  have hbound : C1T33_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T33_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T33.kr, castV p (C1T33.rload d) ≠ 0) ∧
    (∀ d ∈ C1T33.kc, castV p (C1T33.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T33.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T33.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T33_cload_1]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T33_large_integral
#print axioms C1T33_reduced_loads_nonzero

theorem C1T34_small_kills : C1T34.kr.card ≤ 1 ∧ C1T34.kc.card ≤ 1 := by decide +kernel

theorem C1T34_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T34.Integral p := by
  apply C1T34_integral p
  intro hd
  have hpos : 0 < C1T34_den := by decide +kernel
  have hbound : C1T34_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T34_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T34.kr, castV p (C1T34.rload d) ≠ 0) ∧
    (∀ d ∈ C1T34.kc, castV p (C1T34.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T34.kr = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T34_rload_1]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T34.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T34_large_integral
#print axioms C1T34_reduced_loads_nonzero

theorem C1T35_small_kills : C1T35.kr.card ≤ 1 ∧ C1T35.kc.card ≤ 1 := by decide +kernel

theorem C1T35_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T35.Integral p := by
  apply C1T35_integral p
  intro hd
  have hpos : 0 < C1T35_den := by decide +kernel
  have hbound : C1T35_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T35_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T35.kr, castV p (C1T35.rload d) ≠ 0) ∧
    (∀ d ∈ C1T35.kc, castV p (C1T35.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T35.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T35_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (-7 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T35.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T35_large_integral
#print axioms C1T35_reduced_loads_nonzero

theorem C1T36_small_kills : C1T36.kr.card ≤ 1 ∧ C1T36.kc.card ≤ 1 := by decide +kernel

theorem C1T36_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T36.Integral p := by
  apply C1T36_integral p
  intro hd
  have hpos : 0 < C1T36_den := by decide +kernel
  have hbound : C1T36_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T36_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T36.kr, castV p (C1T36.rload d) ≠ 0) ∧
    (∀ d ∈ C1T36.kc, castV p (C1T36.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T36.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T36.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T36_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (-7 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T36_large_integral
#print axioms C1T36_reduced_loads_nonzero

theorem C1T37_small_kills : C1T37.kr.card ≤ 1 ∧ C1T37.kc.card ≤ 1 := by decide +kernel

theorem C1T37_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T37.Integral p := by
  apply C1T37_integral p
  intro hd
  have hpos : 0 < C1T37_den := by decide +kernel
  have hbound : C1T37_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T37_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T37.kr, castV p (C1T37.rload d) ≠ 0) ∧
    (∀ d ∈ C1T37.kc, castV p (C1T37.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T37.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T37_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T37.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T37_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T37_large_integral
#print axioms C1T37_reduced_loads_nonzero

theorem C1T38_small_kills : C1T38.kr.card ≤ 1 ∧ C1T38.kc.card ≤ 1 := by decide +kernel

theorem C1T38_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T38.Integral p := by
  apply C1T38_integral p
  intro hd
  have hpos : 0 < C1T38_den := by decide +kernel
  have hbound : C1T38_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T38_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T38.kr, castV p (C1T38.rload d) ≠ 0) ∧
    (∀ d ∈ C1T38.kc, castV p (C1T38.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T38.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T38_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C1T38.kc = ∅ := rfl
    simp [he] at hd

#print axioms C1T38_large_integral
#print axioms C1T38_reduced_loads_nonzero

theorem C1T39_small_kills : C1T39.kr.card ≤ 1 ∧ C1T39.kc.card ≤ 1 := by decide +kernel

theorem C1T39_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C1T39.Integral p := by
  apply C1T39_integral p
  intro hd
  have hpos : 0 < C1T39_den := by decide +kernel
  have hbound : C1T39_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C1T39_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C1T39.kr, castV p (C1T39.rload d) ≠ 0) ∧
    (∀ d ∈ C1T39.kc, castV p (C1T39.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C1T39.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C1T39.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C1T39_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C1T39_large_integral
#print axioms C1T39_reduced_loads_nonzero

end CatalanCore.Uniform.Bank.Sevenths.RankLoads
