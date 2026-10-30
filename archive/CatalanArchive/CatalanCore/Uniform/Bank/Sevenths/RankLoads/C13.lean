import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C13
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData
theorem C13T00_small_kills : C13T00.kr.card ≤ 1 ∧ C13T00.kc.card ≤ 1 := by decide +kernel

theorem C13T00_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T00.Integral p := by
  apply C13T00_integral p
  intro hd
  have hpos : 0 < C13T00_den := by decide +kernel
  have hbound : C13T00_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T00_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T00.kr, castV p (C13T00.rload d) ≠ 0) ∧
    (∀ d ∈ C13T00.kc, castV p (C13T00.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T00.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T00_rload_6]
    exact rank_castV_ne_zero_of_fst p ((395304946674811193973238466588293 / 1356623644835486562081792240411000), (-683210031796143901343965148836559 / 4069870934506459686245376721233000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T00.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T00_large_integral
#print axioms C13T00_reduced_loads_nonzero

theorem C13T01_small_kills : C13T01.kr.card ≤ 1 ∧ C13T01.kc.card ≤ 1 := by decide +kernel

theorem C13T01_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T01.Integral p := by
  apply C13T01_integral p
  intro hd
  have hpos : 0 < C13T01_den := by decide +kernel
  have hbound : C13T01_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T01_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T01.kr, castV p (C13T01.rload d) ≠ 0) ∧
    (∀ d ∈ C13T01.kc, castV p (C13T01.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T01.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T01.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T01_cload_6]
    exact rank_castV_ne_zero_of_fst p ((395304946674811193973238466588293 / 1356623644835486562081792240411000), (-683210031796143901343965148836559 / 4069870934506459686245376721233000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T01_large_integral
#print axioms C13T01_reduced_loads_nonzero

theorem C13T02_small_kills : C13T02.kr.card ≤ 1 ∧ C13T02.kc.card ≤ 1 := by decide +kernel

theorem C13T02_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T02.Integral p := by
  apply C13T02_integral p
  intro hd
  have hpos : 0 < C13T02_den := by decide +kernel
  have hbound : C13T02_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T02_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T02.kr, castV p (C13T02.rload d) ≠ 0) ∧
    (∀ d ∈ C13T02.kc, castV p (C13T02.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T02.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T02_rload_6]
    exact rank_castV_ne_zero_of_fst p ((6781764726127563921518437768951415485808160811 / 8195140102591842847975581774647508295351852500), (-3808678665034229636448146109902714673314709083 / 15479709082673480935064987796556404557886832500)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T02.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T02_large_integral
#print axioms C13T02_reduced_loads_nonzero

theorem C13T03_small_kills : C13T03.kr.card ≤ 1 ∧ C13T03.kc.card ≤ 1 := by decide +kernel

theorem C13T03_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T03.Integral p := by
  apply C13T03_integral p
  intro hd
  have hpos : 0 < C13T03_den := by decide +kernel
  have hbound : C13T03_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T03_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T03.kr, castV p (C13T03.rload d) ≠ 0) ∧
    (∀ d ∈ C13T03.kc, castV p (C13T03.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T03.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T03.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T03_cload_6]
    exact rank_castV_ne_zero_of_fst p ((6781764726127563921518437768951415485808160811 / 8195140102591842847975581774647508295351852500), (-3808678665034229636448146109902714673314709083 / 15479709082673480935064987796556404557886832500)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T03_large_integral
#print axioms C13T03_reduced_loads_nonzero

theorem C13T04_small_kills : C13T04.kr.card ≤ 1 ∧ C13T04.kc.card ≤ 1 := by decide +kernel

theorem C13T04_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T04.Integral p := by
  apply C13T04_integral p
  intro hd
  have hpos : 0 < C13T04_den := by decide +kernel
  have hbound : C13T04_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T04_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T04.kr, castV p (C13T04.rload d) ≠ 0) ∧
    (∀ d ∈ C13T04.kc, castV p (C13T04.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T04.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T04.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T04_large_integral
#print axioms C13T04_reduced_loads_nonzero

theorem C13T05_small_kills : C13T05.kr.card ≤ 1 ∧ C13T05.kc.card ≤ 1 := by decide +kernel

theorem C13T05_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T05.Integral p := by
  apply C13T05_integral p
  intro hd
  have hpos : 0 < C13T05_den := by decide +kernel
  have hbound : C13T05_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T05_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T05.kr, castV p (C13T05.rload d) ≠ 0) ∧
    (∀ d ∈ C13T05.kc, castV p (C13T05.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T05.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T05.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T05_cload_5]
    exact rank_castV_ne_zero_of_fst p ((43799018387332640851662856305721 / 54128017442428290423669966021000), (-4446727150550975595458036743817 / 18042672480809430141223322007000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T05_large_integral
#print axioms C13T05_reduced_loads_nonzero

theorem C13T06_small_kills : C13T06.kr.card ≤ 1 ∧ C13T06.kc.card ≤ 1 := by decide +kernel

theorem C13T06_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T06.Integral p := by
  apply C13T06_integral p
  intro hd
  have hpos : 0 < C13T06_den := by decide +kernel
  have hbound : C13T06_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T06_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T06.kr, castV p (C13T06.rload d) ≠ 0) ∧
    (∀ d ∈ C13T06.kc, castV p (C13T06.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T06.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T06_rload_5]
    exact rank_castV_ne_zero_of_fst p ((43799018387332640851662856305721 / 54128017442428290423669966021000), (-4446727150550975595458036743817 / 18042672480809430141223322007000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T06.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T06_large_integral
#print axioms C13T06_reduced_loads_nonzero

theorem C13T07_small_kills : C13T07.kr.card ≤ 1 ∧ C13T07.kc.card ≤ 1 := by decide +kernel

theorem C13T07_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T07.Integral p := by
  apply C13T07_integral p
  intro hd
  have hpos : 0 < C13T07_den := by decide +kernel
  have hbound : C13T07_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T07_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T07.kr, castV p (C13T07.rload d) ≠ 0) ∧
    (∀ d ∈ C13T07.kc, castV p (C13T07.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T07.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T07.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T07_large_integral
#print axioms C13T07_reduced_loads_nonzero

theorem C13T08_small_kills : C13T08.kr.card ≤ 1 ∧ C13T08.kc.card ≤ 1 := by decide +kernel

theorem C13T08_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T08.Integral p := by
  apply C13T08_integral p
  intro hd
  have hpos : 0 < C13T08_den := by decide +kernel
  have hbound : C13T08_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T08_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T08.kr, castV p (C13T08.rload d) ≠ 0) ∧
    (∀ d ∈ C13T08.kc, castV p (C13T08.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T08.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T08.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T08_cload_5]
    exact rank_castV_ne_zero_of_fst p ((16145126832533680037 / 94056030380121147000), (-380708984950188733 / 2411693086669773000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T08_large_integral
#print axioms C13T08_reduced_loads_nonzero

theorem C13T09_small_kills : C13T09.kr.card ≤ 1 ∧ C13T09.kc.card ≤ 1 := by decide +kernel

theorem C13T09_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T09.Integral p := by
  apply C13T09_integral p
  intro hd
  have hpos : 0 < C13T09_den := by decide +kernel
  have hbound : C13T09_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T09_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T09.kr, castV p (C13T09.rload d) ≠ 0) ∧
    (∀ d ∈ C13T09.kc, castV p (C13T09.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T09.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T09_rload_5]
    exact rank_castV_ne_zero_of_fst p ((16145126832533680037 / 94056030380121147000), (-380708984950188733 / 2411693086669773000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T09.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T09_large_integral
#print axioms C13T09_reduced_loads_nonzero

theorem C13T10_small_kills : C13T10.kr.card ≤ 1 ∧ C13T10.kc.card ≤ 1 := by decide +kernel

theorem C13T10_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T10.Integral p := by
  apply C13T10_integral p
  intro hd
  have hpos : 0 < C13T10_den := by decide +kernel
  have hbound : C13T10_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T10_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T10.kr, castV p (C13T10.rload d) ≠ 0) ∧
    (∀ d ∈ C13T10.kc, castV p (C13T10.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T10.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T10.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T10_large_integral
#print axioms C13T10_reduced_loads_nonzero

theorem C13T11_small_kills : C13T11.kr.card ≤ 1 ∧ C13T11.kc.card ≤ 1 := by decide +kernel

theorem C13T11_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T11.Integral p := by
  apply C13T11_integral p
  intro hd
  have hpos : 0 < C13T11_den := by decide +kernel
  have hbound : C13T11_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T11_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T11.kr, castV p (C13T11.rload d) ≠ 0) ∧
    (∀ d ∈ C13T11.kc, castV p (C13T11.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T11.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T11.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T11_large_integral
#print axioms C13T11_reduced_loads_nonzero

theorem C13T12_small_kills : C13T12.kr.card ≤ 1 ∧ C13T12.kc.card ≤ 1 := by decide +kernel

theorem C13T12_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T12.Integral p := by
  apply C13T12_integral p
  intro hd
  have hpos : 0 < C13T12_den := by decide +kernel
  have hbound : C13T12_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T12_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T12.kr, castV p (C13T12.rload d) ≠ 0) ∧
    (∀ d ∈ C13T12.kc, castV p (C13T12.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T12.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T12_rload_4]
    exact rank_castV_ne_zero_of_fst p ((75744137104057904693 / 96391624834621345320), (-2655682076987821727 / 10710180537180149480)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T12.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T12_large_integral
#print axioms C13T12_reduced_loads_nonzero

theorem C13T13_small_kills : C13T13.kr.card ≤ 1 ∧ C13T13.kc.card ≤ 1 := by decide +kernel

theorem C13T13_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T13.Integral p := by
  apply C13T13_integral p
  intro hd
  have hpos : 0 < C13T13_den := by decide +kernel
  have hbound : C13T13_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T13_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T13.kr, castV p (C13T13.rload d) ≠ 0) ∧
    (∀ d ∈ C13T13.kc, castV p (C13T13.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T13.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T13.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T13_cload_4]
    exact rank_castV_ne_zero_of_fst p ((75744137104057904693 / 96391624834621345320), (-2655682076987821727 / 10710180537180149480)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T13_large_integral
#print axioms C13T13_reduced_loads_nonzero

theorem C13T14_small_kills : C13T14.kr.card ≤ 1 ∧ C13T14.kc.card ≤ 1 := by decide +kernel

theorem C13T14_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T14.Integral p := by
  apply C13T14_integral p
  intro hd
  have hpos : 0 < C13T14_den := by decide +kernel
  have hbound : C13T14_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T14_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T14.kr, castV p (C13T14.rload d) ≠ 0) ∧
    (∀ d ∈ C13T14.kc, castV p (C13T14.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T14.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T14_rload_4]
    exact rank_castV_ne_zero_of_fst p ((-597592459 / 55304875080), (-34258419 / 236345620)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T14.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T14_large_integral
#print axioms C13T14_reduced_loads_nonzero

theorem C13T15_small_kills : C13T15.kr.card ≤ 1 ∧ C13T15.kc.card ≤ 1 := by decide +kernel

theorem C13T15_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T15.Integral p := by
  apply C13T15_integral p
  intro hd
  have hpos : 0 < C13T15_den := by decide +kernel
  have hbound : C13T15_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T15_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T15.kr, castV p (C13T15.rload d) ≠ 0) ∧
    (∀ d ∈ C13T15.kc, castV p (C13T15.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T15.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T15.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T15_cload_4]
    exact rank_castV_ne_zero_of_fst p ((-597592459 / 55304875080), (-34258419 / 236345620)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T15_large_integral
#print axioms C13T15_reduced_loads_nonzero

theorem C13T16_small_kills : C13T16.kr.card ≤ 1 ∧ C13T16.kc.card ≤ 1 := by decide +kernel

theorem C13T16_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T16.Integral p := by
  apply C13T16_integral p
  intro hd
  have hpos : 0 < C13T16_den := by decide +kernel
  have hbound : C13T16_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T16_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T16.kr, castV p (C13T16.rload d) ≠ 0) ∧
    (∀ d ∈ C13T16.kc, castV p (C13T16.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T16.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T16.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T16_large_integral
#print axioms C13T16_reduced_loads_nonzero

theorem C13T17_small_kills : C13T17.kr.card ≤ 1 ∧ C13T17.kc.card ≤ 1 := by decide +kernel

theorem C13T17_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T17.Integral p := by
  apply C13T17_integral p
  intro hd
  have hpos : 0 < C13T17_den := by decide +kernel
  have hbound : C13T17_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T17_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T17.kr, castV p (C13T17.rload d) ≠ 0) ∧
    (∀ d ∈ C13T17.kc, castV p (C13T17.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T17.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T17.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T17_large_integral
#print axioms C13T17_reduced_loads_nonzero

theorem C13T18_small_kills : C13T18.kr.card ≤ 1 ∧ C13T18.kc.card ≤ 1 := by decide +kernel

theorem C13T18_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T18.Integral p := by
  apply C13T18_integral p
  intro hd
  have hpos : 0 < C13T18_den := by decide +kernel
  have hbound : C13T18_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T18_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T18.kr, castV p (C13T18.rload d) ≠ 0) ∧
    (∀ d ∈ C13T18.kc, castV p (C13T18.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T18.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T18.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T18_cload_3]
    exact rank_castV_ne_zero_of_fst p ((8924952966103 / 11820280388670), (-993366669781 / 3940093462890)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T18_large_integral
#print axioms C13T18_reduced_loads_nonzero

theorem C13T19_small_kills : C13T19.kr.card ≤ 1 ∧ C13T19.kc.card ≤ 1 := by decide +kernel

theorem C13T19_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T19.Integral p := by
  apply C13T19_integral p
  intro hd
  have hpos : 0 < C13T19_den := by decide +kernel
  have hbound : C13T19_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T19_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T19.kr, castV p (C13T19.rload d) ≠ 0) ∧
    (∀ d ∈ C13T19.kc, castV p (C13T19.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T19.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T19_rload_3]
    exact rank_castV_ne_zero_of_fst p ((8924952966103 / 11820280388670), (-993366669781 / 3940093462890)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T19.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T19_large_integral
#print axioms C13T19_reduced_loads_nonzero

theorem C13T20_small_kills : C13T20.kr.card ≤ 1 ∧ C13T20.kc.card ≤ 1 := by decide +kernel

theorem C13T20_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T20.Integral p := by
  apply C13T20_integral p
  intro hd
  have hpos : 0 < C13T20_den := by decide +kernel
  have hbound : C13T20_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T20_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T20.kr, castV p (C13T20.rload d) ≠ 0) ∧
    (∀ d ∈ C13T20.kc, castV p (C13T20.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T20.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T20.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T20_cload_3]
    exact rank_castV_ne_zero_of_fst p ((-35029 / 104130), (-4427 / 34710)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T20_large_integral
#print axioms C13T20_reduced_loads_nonzero

theorem C13T21_small_kills : C13T21.kr.card ≤ 1 ∧ C13T21.kc.card ≤ 1 := by decide +kernel

theorem C13T21_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T21.Integral p := by
  apply C13T21_integral p
  intro hd
  have hpos : 0 < C13T21_den := by decide +kernel
  have hbound : C13T21_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T21_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T21.kr, castV p (C13T21.rload d) ≠ 0) ∧
    (∀ d ∈ C13T21.kc, castV p (C13T21.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T21.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T21_rload_3]
    exact rank_castV_ne_zero_of_fst p ((-35029 / 104130), (-4427 / 34710)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T21.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T21_large_integral
#print axioms C13T21_reduced_loads_nonzero

theorem C13T22_small_kills : C13T22.kr.card ≤ 1 ∧ C13T22.kc.card ≤ 1 := by decide +kernel

theorem C13T22_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T22.Integral p := by
  apply C13T22_integral p
  intro hd
  have hpos : 0 < C13T22_den := by decide +kernel
  have hbound : C13T22_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T22_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T22.kr, castV p (C13T22.rload d) ≠ 0) ∧
    (∀ d ∈ C13T22.kc, castV p (C13T22.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T22.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T22.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T22_large_integral
#print axioms C13T22_reduced_loads_nonzero

theorem C13T23_small_kills : C13T23.kr.card ≤ 1 ∧ C13T23.kc.card ≤ 1 := by decide +kernel

theorem C13T23_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T23.Integral p := by
  apply C13T23_integral p
  intro hd
  have hpos : 0 < C13T23_den := by decide +kernel
  have hbound : C13T23_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T23_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T23.kr, castV p (C13T23.rload d) ≠ 0) ∧
    (∀ d ∈ C13T23.kc, castV p (C13T23.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T23.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T23.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T23_large_integral
#print axioms C13T23_reduced_loads_nonzero

theorem C13T24_small_kills : C13T24.kr.card ≤ 1 ∧ C13T24.kc.card ≤ 1 := by decide +kernel

theorem C13T24_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T24.Integral p := by
  apply C13T24_integral p
  intro hd
  have hpos : 0 < C13T24_den := by decide +kernel
  have hbound : C13T24_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T24_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T24.kr, castV p (C13T24.rload d) ≠ 0) ∧
    (∀ d ∈ C13T24.kc, castV p (C13T24.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T24.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T24_rload_2]
    exact rank_castV_ne_zero_of_fst p ((13674301 / 19166290), (-1167899 / 4422990)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T24.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T24_large_integral
#print axioms C13T24_reduced_loads_nonzero

theorem C13T25_small_kills : C13T25.kr.card ≤ 1 ∧ C13T25.kc.card ≤ 1 := by decide +kernel

theorem C13T25_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T25.Integral p := by
  apply C13T25_integral p
  intro hd
  have hpos : 0 < C13T25_den := by decide +kernel
  have hbound : C13T25_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T25_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T25.kr, castV p (C13T25.rload d) ≠ 0) ∧
    (∀ d ∈ C13T25.kc, castV p (C13T25.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T25.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T25.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T25_cload_2]
    exact rank_castV_ne_zero_of_fst p ((13674301 / 19166290), (-1167899 / 4422990)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T25_large_integral
#print axioms C13T25_reduced_loads_nonzero

theorem C13T26_small_kills : C13T26.kr.card ≤ 1 ∧ C13T26.kc.card ≤ 1 := by decide +kernel

theorem C13T26_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T26.Integral p := by
  apply C13T26_integral p
  intro hd
  have hpos : 0 < C13T26_den := by decide +kernel
  have hbound : C13T26_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T26_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T26.kr, castV p (C13T26.rload d) ≠ 0) ∧
    (∀ d ∈ C13T26.kc, castV p (C13T26.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T26.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T26_rload_2]
    exact rank_castV_ne_zero_of_fst p ((-46 / 39), (-4 / 39)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T26.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T26_large_integral
#print axioms C13T26_reduced_loads_nonzero

theorem C13T27_small_kills : C13T27.kr.card ≤ 1 ∧ C13T27.kc.card ≤ 1 := by decide +kernel

theorem C13T27_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T27.Integral p := by
  apply C13T27_integral p
  intro hd
  have hpos : 0 < C13T27_den := by decide +kernel
  have hbound : C13T27_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T27_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T27.kr, castV p (C13T27.rload d) ≠ 0) ∧
    (∀ d ∈ C13T27.kc, castV p (C13T27.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T27.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T27.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T27_cload_2]
    exact rank_castV_ne_zero_of_fst p ((-46 / 39), (-4 / 39)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T27_large_integral
#print axioms C13T27_reduced_loads_nonzero

theorem C13T28_small_kills : C13T28.kr.card ≤ 1 ∧ C13T28.kc.card ≤ 1 := by decide +kernel

theorem C13T28_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T28.Integral p := by
  apply C13T28_integral p
  intro hd
  have hpos : 0 < C13T28_den := by decide +kernel
  have hbound : C13T28_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T28_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T28.kr, castV p (C13T28.rload d) ≠ 0) ∧
    (∀ d ∈ C13T28.kc, castV p (C13T28.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T28.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T28.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T28_large_integral
#print axioms C13T28_reduced_loads_nonzero

theorem C13T29_small_kills : C13T29.kr.card ≤ 1 ∧ C13T29.kc.card ≤ 1 := by decide +kernel

theorem C13T29_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T29.Integral p := by
  apply C13T29_integral p
  intro hd
  have hpos : 0 < C13T29_den := by decide +kernel
  have hbound : C13T29_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T29_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T29.kr, castV p (C13T29.rload d) ≠ 0) ∧
    (∀ d ∈ C13T29.kc, castV p (C13T29.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T29.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T29.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T29_large_integral
#print axioms C13T29_reduced_loads_nonzero

theorem C13T30_small_kills : C13T30.kr.card ≤ 1 ∧ C13T30.kc.card ≤ 1 := by decide +kernel

theorem C13T30_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T30.Integral p := by
  apply C13T30_integral p
  intro hd
  have hpos : 0 < C13T30_den := by decide +kernel
  have hbound : C13T30_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T30_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T30.kr, castV p (C13T30.rload d) ≠ 0) ∧
    (∀ d ∈ C13T30.kc, castV p (C13T30.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T30.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T30.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T30_cload_1]
    exact rank_castV_ne_zero_of_fst p ((421 / 637), (-13 / 42)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T30_large_integral
#print axioms C13T30_reduced_loads_nonzero

theorem C13T31_small_kills : C13T31.kr.card ≤ 1 ∧ C13T31.kc.card ≤ 1 := by decide +kernel

theorem C13T31_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T31.Integral p := by
  apply C13T31_integral p
  intro hd
  have hpos : 0 < C13T31_den := by decide +kernel
  have hbound : C13T31_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T31_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T31.kr, castV p (C13T31.rload d) ≠ 0) ∧
    (∀ d ∈ C13T31.kc, castV p (C13T31.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T31.kr = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T31_rload_1]
    exact rank_castV_ne_zero_of_fst p ((421 / 637), (-13 / 42)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T31.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T31_large_integral
#print axioms C13T31_reduced_loads_nonzero

theorem C13T32_small_kills : C13T32.kr.card ≤ 1 ∧ C13T32.kc.card ≤ 1 := by decide +kernel

theorem C13T32_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T32.Integral p := by
  apply C13T32_integral p
  intro hd
  have hpos : 0 < C13T32_den := by decide +kernel
  have hbound : C13T32_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T32_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T32.kr, castV p (C13T32.rload d) ≠ 0) ∧
    (∀ d ∈ C13T32.kc, castV p (C13T32.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T32.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T32.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T32_cload_1]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T32_large_integral
#print axioms C13T32_reduced_loads_nonzero

theorem C13T33_small_kills : C13T33.kr.card ≤ 1 ∧ C13T33.kc.card ≤ 1 := by decide +kernel

theorem C13T33_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T33.Integral p := by
  apply C13T33_integral p
  intro hd
  have hpos : 0 < C13T33_den := by decide +kernel
  have hbound : C13T33_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T33_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T33.kr, castV p (C13T33.rload d) ≠ 0) ∧
    (∀ d ∈ C13T33.kc, castV p (C13T33.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T33.kr = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T33_rload_1]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T33.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T33_large_integral
#print axioms C13T33_reduced_loads_nonzero

theorem C13T34_small_kills : C13T34.kr.card ≤ 1 ∧ C13T34.kc.card ≤ 1 := by decide +kernel

theorem C13T34_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T34.Integral p := by
  apply C13T34_integral p
  intro hd
  have hpos : 0 < C13T34_den := by decide +kernel
  have hbound : C13T34_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T34_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T34.kr, castV p (C13T34.rload d) ≠ 0) ∧
    (∀ d ∈ C13T34.kc, castV p (C13T34.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T34.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T34.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T34_large_integral
#print axioms C13T34_reduced_loads_nonzero

theorem C13T35_small_kills : C13T35.kr.card ≤ 1 ∧ C13T35.kc.card ≤ 1 := by decide +kernel

theorem C13T35_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T35.Integral p := by
  apply C13T35_integral p
  intro hd
  have hpos : 0 < C13T35_den := by decide +kernel
  have hbound : C13T35_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T35_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T35.kr, castV p (C13T35.rload d) ≠ 0) ∧
    (∀ d ∈ C13T35.kc, castV p (C13T35.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T35.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T35_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T35.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T35_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T35_large_integral
#print axioms C13T35_reduced_loads_nonzero

theorem C13T36_small_kills : C13T36.kr.card ≤ 1 ∧ C13T36.kc.card ≤ 1 := by decide +kernel

theorem C13T36_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T36.Integral p := by
  apply C13T36_integral p
  intro hd
  have hpos : 0 < C13T36_den := by decide +kernel
  have hbound : C13T36_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T36_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T36.kr, castV p (C13T36.rload d) ≠ 0) ∧
    (∀ d ∈ C13T36.kc, castV p (C13T36.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T36.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T36_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (-7 / 6)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T36.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T36_large_integral
#print axioms C13T36_reduced_loads_nonzero

theorem C13T37_small_kills : C13T37.kr.card ≤ 1 ∧ C13T37.kc.card ≤ 1 := by decide +kernel

theorem C13T37_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T37.Integral p := by
  apply C13T37_integral p
  intro hd
  have hpos : 0 < C13T37_den := by decide +kernel
  have hbound : C13T37_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T37_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T37.kr, castV p (C13T37.rload d) ≠ 0) ∧
    (∀ d ∈ C13T37.kc, castV p (C13T37.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T37.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T37.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T37_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (-7 / 6)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T37_large_integral
#print axioms C13T37_reduced_loads_nonzero

theorem C13T38_small_kills : C13T38.kr.card ≤ 1 ∧ C13T38.kc.card ≤ 1 := by decide +kernel

theorem C13T38_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T38.Integral p := by
  apply C13T38_integral p
  intro hd
  have hpos : 0 < C13T38_den := by decide +kernel
  have hbound : C13T38_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T38_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T38.kr, castV p (C13T38.rload d) ≠ 0) ∧
    (∀ d ∈ C13T38.kc, castV p (C13T38.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T38.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T38_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C13T38.kc = ∅ := rfl
    simp [he] at hd

#print axioms C13T38_large_integral
#print axioms C13T38_reduced_loads_nonzero

theorem C13T39_small_kills : C13T39.kr.card ≤ 1 ∧ C13T39.kc.card ≤ 1 := by decide +kernel

theorem C13T39_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C13T39.Integral p := by
  apply C13T39_integral p
  intro hd
  have hpos : 0 < C13T39_den := by decide +kernel
  have hbound : C13T39_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C13T39_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C13T39.kr, castV p (C13T39.rload d) ≠ 0) ∧
    (∀ d ∈ C13T39.kc, castV p (C13T39.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C13T39.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C13T39.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C13T39_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C13T39_large_integral
#print axioms C13T39_reduced_loads_nonzero

end CatalanCore.Uniform.Bank.Sevenths.RankLoads
