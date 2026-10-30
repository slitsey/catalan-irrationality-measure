import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C5
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData
theorem C5T00_small_kills : C5T00.kr.card ≤ 1 ∧ C5T00.kc.card ≤ 1 := by decide +kernel

theorem C5T00_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T00.Integral p := by
  apply C5T00_integral p
  intro hd
  have hpos : 0 < C5T00_den := by decide +kernel
  have hbound : C5T00_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T00_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T00.kr, castV p (C5T00.rload d) ≠ 0) ∧
    (∀ d ∈ C5T00.kc, castV p (C5T00.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T00.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T00_rload_6]
    exact rank_castV_ne_zero_of_fst p ((230471884324722397994169594074547 / 1079406927775970636862169002845120), (-652466848665211800897598990869389 / 539703463887985318431084501422560)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T00.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T00_large_integral
#print axioms C5T00_reduced_loads_nonzero

theorem C5T01_small_kills : C5T01.kr.card ≤ 1 ∧ C5T01.kc.card ≤ 1 := by decide +kernel

theorem C5T01_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T01.Integral p := by
  apply C5T01_integral p
  intro hd
  have hpos : 0 < C5T01_den := by decide +kernel
  have hbound : C5T01_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T01_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T01.kr, castV p (C5T01.rload d) ≠ 0) ∧
    (∀ d ∈ C5T01.kc, castV p (C5T01.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T01.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T01.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T01_cload_6]
    exact rank_castV_ne_zero_of_fst p ((230471884324722397994169594074547 / 1079406927775970636862169002845120), (-652466848665211800897598990869389 / 539703463887985318431084501422560)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T01_large_integral
#print axioms C5T01_reduced_loads_nonzero

theorem C5T02_small_kills : C5T02.kr.card ≤ 1 ∧ C5T02.kc.card ≤ 1 := by decide +kernel

theorem C5T02_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T02.Integral p := by
  apply C5T02_integral p
  intro hd
  have hpos : 0 < C5T02_den := by decide +kernel
  have hbound : C5T02_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T02_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T02.kr, castV p (C5T02.rload d) ≠ 0) ∧
    (∀ d ∈ C5T02.kc, castV p (C5T02.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T02.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T02_rload_6]
    exact rank_castV_ne_zero_of_fst p ((44937261743829484335362526866014588927699013017 / 46408277013154567295820860566182756770141768064), (-82843324323017664427375250907837778036718237777 / 46408277013154567295820860566182756770141768064)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T02.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T02_large_integral
#print axioms C5T02_reduced_loads_nonzero

theorem C5T03_small_kills : C5T03.kr.card ≤ 1 ∧ C5T03.kc.card ≤ 1 := by decide +kernel

theorem C5T03_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T03.Integral p := by
  apply C5T03_integral p
  intro hd
  have hpos : 0 < C5T03_den := by decide +kernel
  have hbound : C5T03_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T03_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T03.kr, castV p (C5T03.rload d) ≠ 0) ∧
    (∀ d ∈ C5T03.kc, castV p (C5T03.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T03.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T03.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T03_cload_6]
    exact rank_castV_ne_zero_of_fst p ((44937261743829484335362526866014588927699013017 / 46408277013154567295820860566182756770141768064), (-82843324323017664427375250907837778036718237777 / 46408277013154567295820860566182756770141768064)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T03_large_integral
#print axioms C5T03_reduced_loads_nonzero

theorem C5T04_small_kills : C5T04.kr.card ≤ 1 ∧ C5T04.kc.card ≤ 1 := by decide +kernel

theorem C5T04_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T04.Integral p := by
  apply C5T04_integral p
  intro hd
  have hpos : 0 < C5T04_den := by decide +kernel
  have hbound : C5T04_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T04_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T04.kr, castV p (C5T04.rload d) ≠ 0) ∧
    (∀ d ∈ C5T04.kc, castV p (C5T04.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T04.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T04.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T04_large_integral
#print axioms C5T04_reduced_loads_nonzero

theorem C5T05_small_kills : C5T05.kr.card ≤ 1 ∧ C5T05.kc.card ≤ 1 := by decide +kernel

theorem C5T05_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T05.Integral p := by
  apply C5T05_integral p
  intro hd
  have hpos : 0 < C5T05_den := by decide +kernel
  have hbound : C5T05_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T05_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T05.kr, castV p (C5T05.rload d) ≠ 0) ∧
    (∀ d ∈ C5T05.kc, castV p (C5T05.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T05.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T05.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T05_cload_5]
    exact rank_castV_ne_zero_of_fst p ((65033412544380867527211715151743 / 67391433797389529022169033434080), (-3736713636642434958236829974636717 / 2089134447719075399687240036456480)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T05_large_integral
#print axioms C5T05_reduced_loads_nonzero

theorem C5T06_small_kills : C5T06.kr.card ≤ 1 ∧ C5T06.kc.card ≤ 1 := by decide +kernel

theorem C5T06_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T06.Integral p := by
  apply C5T06_integral p
  intro hd
  have hpos : 0 < C5T06_den := by decide +kernel
  have hbound : C5T06_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T06_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T06.kr, castV p (C5T06.rload d) ≠ 0) ∧
    (∀ d ∈ C5T06.kc, castV p (C5T06.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T06.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T06_rload_5]
    exact rank_castV_ne_zero_of_fst p ((65033412544380867527211715151743 / 67391433797389529022169033434080), (-3736713636642434958236829974636717 / 2089134447719075399687240036456480)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T06.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T06_large_integral
#print axioms C5T06_reduced_loads_nonzero

theorem C5T07_small_kills : C5T07.kr.card ≤ 1 ∧ C5T07.kc.card ≤ 1 := by decide +kernel

theorem C5T07_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T07.Integral p := by
  apply C5T07_integral p
  intro hd
  have hpos : 0 < C5T07_den := by decide +kernel
  have hbound : C5T07_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T07_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T07.kr, castV p (C5T07.rload d) ≠ 0) ∧
    (∀ d ∈ C5T07.kc, castV p (C5T07.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T07.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T07.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T07_large_integral
#print axioms C5T07_reduced_loads_nonzero

theorem C5T08_small_kills : C5T08.kr.card ≤ 1 ∧ C5T08.kc.card ≤ 1 := by decide +kernel

theorem C5T08_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T08.Integral p := by
  apply C5T08_integral p
  intro hd
  have hpos : 0 < C5T08_den := by decide +kernel
  have hbound : C5T08_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T08_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T08.kr, castV p (C5T08.rload d) ≠ 0) ∧
    (∀ d ∈ C5T08.kc, castV p (C5T08.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T08.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T08.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T08_cload_5]
    exact rank_castV_ne_zero_of_fst p ((438775970875049820257 / 6406403291402927140120), (-7327887412246007402443 / 6406403291402927140120)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T08_large_integral
#print axioms C5T08_reduced_loads_nonzero

theorem C5T09_small_kills : C5T09.kr.card ≤ 1 ∧ C5T09.kc.card ≤ 1 := by decide +kernel

theorem C5T09_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T09.Integral p := by
  apply C5T09_integral p
  intro hd
  have hpos : 0 < C5T09_den := by decide +kernel
  have hbound : C5T09_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T09_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T09.kr, castV p (C5T09.rload d) ≠ 0) ∧
    (∀ d ∈ C5T09.kc, castV p (C5T09.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T09.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T09_rload_5]
    exact rank_castV_ne_zero_of_fst p ((438775970875049820257 / 6406403291402927140120), (-7327887412246007402443 / 6406403291402927140120)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T09.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T09_large_integral
#print axioms C5T09_reduced_loads_nonzero

theorem C5T10_small_kills : C5T10.kr.card ≤ 1 ∧ C5T10.kc.card ≤ 1 := by decide +kernel

theorem C5T10_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T10.Integral p := by
  apply C5T10_integral p
  intro hd
  have hpos : 0 < C5T10_den := by decide +kernel
  have hbound : C5T10_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T10_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T10.kr, castV p (C5T10.rload d) ≠ 0) ∧
    (∀ d ∈ C5T10.kc, castV p (C5T10.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T10.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T10.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T10_large_integral
#print axioms C5T10_reduced_loads_nonzero

theorem C5T11_small_kills : C5T11.kr.card ≤ 1 ∧ C5T11.kc.card ≤ 1 := by decide +kernel

theorem C5T11_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T11.Integral p := by
  apply C5T11_integral p
  intro hd
  have hpos : 0 < C5T11_den := by decide +kernel
  have hbound : C5T11_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T11_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T11.kr, castV p (C5T11.rload d) ≠ 0) ∧
    (∀ d ∈ C5T11.kc, castV p (C5T11.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T11.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T11_rload_4]
    exact rank_castV_ne_zero_of_fst p ((6174604212799346502517 / 6425822730968570242880), (-180203690492799970109 / 100403480171383910045)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T11.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T11_large_integral
#print axioms C5T11_reduced_loads_nonzero

theorem C5T12_small_kills : C5T12.kr.card ≤ 1 ∧ C5T12.kc.card ≤ 1 := by decide +kernel

theorem C5T12_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T12.Integral p := by
  apply C5T12_integral p
  intro hd
  have hpos : 0 < C5T12_den := by decide +kernel
  have hbound : C5T12_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T12_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T12.kr, castV p (C5T12.rload d) ≠ 0) ∧
    (∀ d ∈ C5T12.kc, castV p (C5T12.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T12.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T12.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T12_cload_4]
    exact rank_castV_ne_zero_of_fst p ((6174604212799346502517 / 6425822730968570242880), (-180203690492799970109 / 100403480171383910045)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T12_large_integral
#print axioms C5T12_reduced_loads_nonzero

theorem C5T13_small_kills : C5T13.kr.card ≤ 1 ∧ C5T13.kc.card ≤ 1 := by decide +kernel

theorem C5T13_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T13.Integral p := by
  apply C5T13_integral p
  intro hd
  have hpos : 0 < C5T13_den := by decide +kernel
  have hbound : C5T13_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T13_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T13.kr, castV p (C5T13.rload d) ≠ 0) ∧
    (∀ d ∈ C5T13.kc, castV p (C5T13.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T13.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T13.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T13_large_integral
#print axioms C5T13_reduced_loads_nonzero

theorem C5T14_small_kills : C5T14.kr.card ≤ 1 ∧ C5T14.kc.card ≤ 1 := by decide +kernel

theorem C5T14_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T14.Integral p := by
  apply C5T14_integral p
  intro hd
  have hpos : 0 < C5T14_den := by decide +kernel
  have hbound : C5T14_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T14_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T14.kr, castV p (C5T14.rload d) ≠ 0) ∧
    (∀ d ∈ C5T14.kc, castV p (C5T14.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T14.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T14_rload_4]
    exact rank_castV_ne_zero_of_fst p ((-27334535430997 / 175045825432240), (-37058845307039 / 35009165086448)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T14.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T14_large_integral
#print axioms C5T14_reduced_loads_nonzero

theorem C5T15_small_kills : C5T15.kr.card ≤ 1 ∧ C5T15.kc.card ≤ 1 := by decide +kernel

theorem C5T15_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T15.Integral p := by
  apply C5T15_integral p
  intro hd
  have hpos : 0 < C5T15_den := by decide +kernel
  have hbound : C5T15_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T15_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T15.kr, castV p (C5T15.rload d) ≠ 0) ∧
    (∀ d ∈ C5T15.kc, castV p (C5T15.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T15.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T15.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T15_cload_4]
    exact rank_castV_ne_zero_of_fst p ((-27334535430997 / 175045825432240), (-37058845307039 / 35009165086448)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T15_large_integral
#print axioms C5T15_reduced_loads_nonzero

theorem C5T16_small_kills : C5T16.kr.card ≤ 1 ∧ C5T16.kc.card ≤ 1 := by decide +kernel

theorem C5T16_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T16.Integral p := by
  apply C5T16_integral p
  intro hd
  have hpos : 0 < C5T16_den := by decide +kernel
  have hbound : C5T16_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T16_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T16.kr, castV p (C5T16.rload d) ≠ 0) ∧
    (∀ d ∈ C5T16.kc, castV p (C5T16.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T16.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T16.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T16_large_integral
#print axioms C5T16_reduced_loads_nonzero

theorem C5T17_small_kills : C5T17.kr.card ≤ 1 ∧ C5T17.kc.card ≤ 1 := by decide +kernel

theorem C5T17_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T17.Integral p := by
  apply C5T17_integral p
  intro hd
  have hpos : 0 < C5T17_den := by decide +kernel
  have hbound : C5T17_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T17_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T17.kr, castV p (C5T17.rload d) ≠ 0) ∧
    (∀ d ∈ C5T17.kc, castV p (C5T17.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T17.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T17.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T17_cload_3]
    exact rank_castV_ne_zero_of_fst p ((88826886444701 / 92941318035340), (-41973208914319 / 23235329508835)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T17_large_integral
#print axioms C5T17_reduced_loads_nonzero

theorem C5T18_small_kills : C5T18.kr.card ≤ 1 ∧ C5T18.kc.card ≤ 1 := by decide +kernel

theorem C5T18_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T18.Integral p := by
  apply C5T18_integral p
  intro hd
  have hpos : 0 < C5T18_den := by decide +kernel
  have hbound : C5T18_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T18_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T18.kr, castV p (C5T18.rload d) ≠ 0) ∧
    (∀ d ∈ C5T18.kc, castV p (C5T18.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T18.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T18_rload_3]
    exact rank_castV_ne_zero_of_fst p ((88826886444701 / 92941318035340), (-41973208914319 / 23235329508835)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T18.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T18_large_integral
#print axioms C5T18_reduced_loads_nonzero

theorem C5T19_small_kills : C5T19.kr.card ≤ 1 ∧ C5T19.kc.card ≤ 1 := by decide +kernel

theorem C5T19_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T19.Integral p := by
  apply C5T19_integral p
  intro hd
  have hpos : 0 < C5T19_den := by decide +kernel
  have hbound : C5T19_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T19_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T19.kr, castV p (C5T19.rload d) ≠ 0) ∧
    (∀ d ∈ C5T19.kc, castV p (C5T19.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T19.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T19.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T19_large_integral
#print axioms C5T19_reduced_loads_nonzero

theorem C5T20_small_kills : C5T20.kr.card ≤ 1 ∧ C5T20.kc.card ≤ 1 := by decide +kernel

theorem C5T20_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T20.Integral p := by
  apply C5T20_integral p
  intro hd
  have hpos : 0 < C5T20_den := by decide +kernel
  have hbound : C5T20_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T20_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T20.kr, castV p (C5T20.rload d) ≠ 0) ∧
    (∀ d ∈ C5T20.kc, castV p (C5T20.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T20.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T20.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T20_cload_3]
    exact rank_castV_ne_zero_of_fst p ((-26467723 / 46883280), (-3676321 / 3906940)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T20_large_integral
#print axioms C5T20_reduced_loads_nonzero

theorem C5T21_small_kills : C5T21.kr.card ≤ 1 ∧ C5T21.kc.card ≤ 1 := by decide +kernel

theorem C5T21_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T21.Integral p := by
  apply C5T21_integral p
  intro hd
  have hpos : 0 < C5T21_den := by decide +kernel
  have hbound : C5T21_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T21_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T21.kr, castV p (C5T21.rload d) ≠ 0) ∧
    (∀ d ∈ C5T21.kc, castV p (C5T21.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T21.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T21_rload_3]
    exact rank_castV_ne_zero_of_fst p ((-26467723 / 46883280), (-3676321 / 3906940)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T21.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T21_large_integral
#print axioms C5T21_reduced_loads_nonzero

theorem C5T22_small_kills : C5T22.kr.card ≤ 1 ∧ C5T22.kc.card ≤ 1 := by decide +kernel

theorem C5T22_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T22.Integral p := by
  apply C5T22_integral p
  intro hd
  have hpos : 0 < C5T22_den := by decide +kernel
  have hbound : C5T22_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T22_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T22.kr, castV p (C5T22.rload d) ≠ 0) ∧
    (∀ d ∈ C5T22.kc, castV p (C5T22.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T22.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T22.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T22_large_integral
#print axioms C5T22_reduced_loads_nonzero

theorem C5T23_small_kills : C5T23.kr.card ≤ 1 ∧ C5T23.kc.card ≤ 1 := by decide +kernel

theorem C5T23_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T23.Integral p := by
  apply C5T23_integral p
  intro hd
  have hpos : 0 < C5T23_den := by decide +kernel
  have hbound : C5T23_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T23_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T23.kr, castV p (C5T23.rload d) ≠ 0) ∧
    (∀ d ∈ C5T23.kc, castV p (C5T23.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T23.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T23_rload_2]
    exact rank_castV_ne_zero_of_fst p ((35005763 / 36869600), (-1266383 / 691305)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T23.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T23_large_integral
#print axioms C5T23_reduced_loads_nonzero

theorem C5T24_small_kills : C5T24.kr.card ≤ 1 ∧ C5T24.kc.card ≤ 1 := by decide +kernel

theorem C5T24_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T24.Integral p := by
  apply C5T24_integral p
  intro hd
  have hpos : 0 < C5T24_den := by decide +kernel
  have hbound : C5T24_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T24_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T24.kr, castV p (C5T24.rload d) ≠ 0) ∧
    (∀ d ∈ C5T24.kc, castV p (C5T24.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T24.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T24.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T24_cload_2]
    exact rank_castV_ne_zero_of_fst p ((35005763 / 36869600), (-1266383 / 691305)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T24_large_integral
#print axioms C5T24_reduced_loads_nonzero

theorem C5T25_small_kills : C5T25.kr.card ≤ 1 ∧ C5T25.kc.card ≤ 1 := by decide +kernel

theorem C5T25_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T25.Integral p := by
  apply C5T25_integral p
  intro hd
  have hpos : 0 < C5T25_den := by decide +kernel
  have hbound : C5T25_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T25_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T25.kr, castV p (C5T25.rload d) ≠ 0) ∧
    (∀ d ∈ C5T25.kc, castV p (C5T25.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T25.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T25.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T25_large_integral
#print axioms C5T25_reduced_loads_nonzero

theorem C5T26_small_kills : C5T26.kr.card ≤ 1 ∧ C5T26.kc.card ≤ 1 := by decide +kernel

theorem C5T26_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T26.Integral p := by
  apply C5T26_integral p
  intro hd
  have hpos : 0 < C5T26_den := by decide +kernel
  have hbound : C5T26_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T26_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T26.kr, castV p (C5T26.rload d) ≠ 0) ∧
    (∀ d ∈ C5T26.kc, castV p (C5T26.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T26.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T26.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T26_large_integral
#print axioms C5T26_reduced_loads_nonzero

theorem C5T27_small_kills : C5T27.kr.card ≤ 1 ∧ C5T27.kc.card ≤ 1 := by decide +kernel

theorem C5T27_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T27.Integral p := by
  apply C5T27_integral p
  intro hd
  have hpos : 0 < C5T27_den := by decide +kernel
  have hbound : C5T27_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T27_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T27.kr, castV p (C5T27.rload d) ≠ 0) ∧
    (∀ d ∈ C5T27.kc, castV p (C5T27.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T27.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T27_rload_2]
    exact rank_castV_ne_zero_of_fst p ((-197 / 120), (-23 / 30)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T27.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T27_large_integral
#print axioms C5T27_reduced_loads_nonzero

theorem C5T28_small_kills : C5T28.kr.card ≤ 1 ∧ C5T28.kc.card ≤ 1 := by decide +kernel

theorem C5T28_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T28.Integral p := by
  apply C5T28_integral p
  intro hd
  have hpos : 0 < C5T28_den := by decide +kernel
  have hbound : C5T28_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T28_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T28.kr, castV p (C5T28.rload d) ≠ 0) ∧
    (∀ d ∈ C5T28.kc, castV p (C5T28.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T28.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T28.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T28_cload_2]
    exact rank_castV_ne_zero_of_fst p ((-197 / 120), (-23 / 30)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T28_large_integral
#print axioms C5T28_reduced_loads_nonzero

theorem C5T29_small_kills : C5T29.kr.card ≤ 1 ∧ C5T29.kc.card ≤ 1 := by decide +kernel

theorem C5T29_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T29.Integral p := by
  apply C5T29_integral p
  intro hd
  have hpos : 0 < C5T29_den := by decide +kernel
  have hbound : C5T29_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T29_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T29.kr, castV p (C5T29.rload d) ≠ 0) ∧
    (∀ d ∈ C5T29.kc, castV p (C5T29.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T29.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T29.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T29_large_integral
#print axioms C5T29_reduced_loads_nonzero

theorem C5T30_small_kills : C5T30.kr.card ≤ 1 ∧ C5T30.kc.card ≤ 1 := by decide +kernel

theorem C5T30_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T30.Integral p := by
  apply C5T30_integral p
  intro hd
  have hpos : 0 < C5T30_den := by decide +kernel
  have hbound : C5T30_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T30_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T30.kr, castV p (C5T30.rload d) ≠ 0) ∧
    (∀ d ∈ C5T30.kc, castV p (C5T30.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T30.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T30.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T30_cload_1]
    exact rank_castV_ne_zero_of_fst p ((463 / 490), (-40 / 21)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T30_large_integral
#print axioms C5T30_reduced_loads_nonzero

theorem C5T31_small_kills : C5T31.kr.card ≤ 1 ∧ C5T31.kc.card ≤ 1 := by decide +kernel

theorem C5T31_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T31.Integral p := by
  apply C5T31_integral p
  intro hd
  have hpos : 0 < C5T31_den := by decide +kernel
  have hbound : C5T31_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T31_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T31.kr, castV p (C5T31.rload d) ≠ 0) ∧
    (∀ d ∈ C5T31.kc, castV p (C5T31.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T31.kr = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T31_rload_1]
    exact rank_castV_ne_zero_of_fst p ((463 / 490), (-40 / 21)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T31.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T31_large_integral
#print axioms C5T31_reduced_loads_nonzero

theorem C5T32_small_kills : C5T32.kr.card ≤ 1 ∧ C5T32.kc.card ≤ 1 := by decide +kernel

theorem C5T32_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T32.Integral p := by
  apply C5T32_integral p
  intro hd
  have hpos : 0 < C5T32_den := by decide +kernel
  have hbound : C5T32_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T32_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T32.kr, castV p (C5T32.rload d) ≠ 0) ∧
    (∀ d ∈ C5T32.kc, castV p (C5T32.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T32.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T32.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T32_large_integral
#print axioms C5T32_reduced_loads_nonzero

theorem C5T33_small_kills : C5T33.kr.card ≤ 1 ∧ C5T33.kc.card ≤ 1 := by decide +kernel

theorem C5T33_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T33.Integral p := by
  apply C5T33_integral p
  intro hd
  have hpos : 0 < C5T33_den := by decide +kernel
  have hbound : C5T33_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T33_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T33.kr, castV p (C5T33.rload d) ≠ 0) ∧
    (∀ d ∈ C5T33.kc, castV p (C5T33.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T33.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T33.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T33_cload_1]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T33_large_integral
#print axioms C5T33_reduced_loads_nonzero

theorem C5T34_small_kills : C5T34.kr.card ≤ 1 ∧ C5T34.kc.card ≤ 1 := by decide +kernel

theorem C5T34_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T34.Integral p := by
  apply C5T34_integral p
  intro hd
  have hpos : 0 < C5T34_den := by decide +kernel
  have hbound : C5T34_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T34_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T34.kr, castV p (C5T34.rload d) ≠ 0) ∧
    (∀ d ∈ C5T34.kc, castV p (C5T34.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T34.kr = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T34_rload_1]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T34.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T34_large_integral
#print axioms C5T34_reduced_loads_nonzero

theorem C5T35_small_kills : C5T35.kr.card ≤ 1 ∧ C5T35.kc.card ≤ 1 := by decide +kernel

theorem C5T35_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T35.Integral p := by
  apply C5T35_integral p
  intro hd
  have hpos : 0 < C5T35_den := by decide +kernel
  have hbound : C5T35_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T35_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T35.kr, castV p (C5T35.rload d) ≠ 0) ∧
    (∀ d ∈ C5T35.kc, castV p (C5T35.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T35.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T35_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T35.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T35_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T35_large_integral
#print axioms C5T35_reduced_loads_nonzero

theorem C5T36_small_kills : C5T36.kr.card ≤ 1 ∧ C5T36.kc.card ≤ 1 := by decide +kernel

theorem C5T36_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T36.Integral p := by
  apply C5T36_integral p
  intro hd
  have hpos : 0 < C5T36_den := by decide +kernel
  have hbound : C5T36_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T36_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T36.kr, castV p (C5T36.rload d) ≠ 0) ∧
    (∀ d ∈ C5T36.kc, castV p (C5T36.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T36.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T36_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (-7 / 3)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T36.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T36_large_integral
#print axioms C5T36_reduced_loads_nonzero

theorem C5T37_small_kills : C5T37.kr.card ≤ 1 ∧ C5T37.kc.card ≤ 1 := by decide +kernel

theorem C5T37_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T37.Integral p := by
  apply C5T37_integral p
  intro hd
  have hpos : 0 < C5T37_den := by decide +kernel
  have hbound : C5T37_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T37_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T37.kr, castV p (C5T37.rload d) ≠ 0) ∧
    (∀ d ∈ C5T37.kc, castV p (C5T37.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T37.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T37.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T37_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (-7 / 3)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T37_large_integral
#print axioms C5T37_reduced_loads_nonzero

theorem C5T38_small_kills : C5T38.kr.card ≤ 1 ∧ C5T38.kc.card ≤ 1 := by decide +kernel

theorem C5T38_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T38.Integral p := by
  apply C5T38_integral p
  intro hd
  have hpos : 0 < C5T38_den := by decide +kernel
  have hbound : C5T38_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T38_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T38.kr, castV p (C5T38.rload d) ≠ 0) ∧
    (∀ d ∈ C5T38.kc, castV p (C5T38.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T38.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T38_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C5T38.kc = ∅ := rfl
    simp [he] at hd

#print axioms C5T38_large_integral
#print axioms C5T38_reduced_loads_nonzero

theorem C5T39_small_kills : C5T39.kr.card ≤ 1 ∧ C5T39.kc.card ≤ 1 := by decide +kernel

theorem C5T39_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C5T39.Integral p := by
  apply C5T39_integral p
  intro hd
  have hpos : 0 < C5T39_den := by decide +kernel
  have hbound : C5T39_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C5T39_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C5T39.kr, castV p (C5T39.rload d) ≠ 0) ∧
    (∀ d ∈ C5T39.kc, castV p (C5T39.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C5T39.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C5T39.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C5T39_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C5T39_large_integral
#print axioms C5T39_reduced_loads_nonzero

end CatalanCore.Uniform.Bank.Sevenths.RankLoads
