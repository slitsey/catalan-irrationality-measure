import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C11
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData
theorem C11T00_small_kills : C11T00.kr.card ≤ 1 ∧ C11T00.kc.card ≤ 1 := by decide +kernel

theorem C11T00_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T00.Integral p := by
  apply C11T00_integral p
  intro hd
  have hpos : 0 < C11T00_den := by decide +kernel
  have hbound : C11T00_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T00_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T00.kr, castV p (C11T00.rload d) ≠ 0) ∧
    (∀ d ∈ C11T00.kc, castV p (C11T00.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T00.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T00_rload_6]
    exact rank_castV_ne_zero_of_fst p ((1730829760278160905139789902184333487 / 16343077720378337911866161413462200000), (-10560437972615517451291007915544105583 / 4902923316113501373559848424038660000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T00.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T00_large_integral
#print axioms C11T00_reduced_loads_nonzero

theorem C11T01_small_kills : C11T01.kr.card ≤ 1 ∧ C11T01.kc.card ≤ 1 := by decide +kernel

theorem C11T01_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T01.Integral p := by
  apply C11T01_integral p
  intro hd
  have hpos : 0 < C11T01_den := by decide +kernel
  have hbound : C11T01_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T01_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T01.kr, castV p (C11T01.rload d) ≠ 0) ∧
    (∀ d ∈ C11T01.kc, castV p (C11T01.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T01.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T01.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T01_cload_6]
    exact rank_castV_ne_zero_of_fst p ((1730829760278160905139789902184333487 / 16343077720378337911866161413462200000), (-10560437972615517451291007915544105583 / 4902923316113501373559848424038660000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T01_large_integral
#print axioms C11T01_reduced_loads_nonzero

theorem C11T02_small_kills : C11T02.kr.card ≤ 1 ∧ C11T02.kc.card ≤ 1 := by decide +kernel

theorem C11T02_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T02.Integral p := by
  apply C11T02_integral p
  intro hd
  have hpos : 0 < C11T02_den := by decide +kernel
  have hbound : C11T02_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T02_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T02.kr, castV p (C11T02.rload d) ≠ 0) ∧
    (∀ d ∈ C11T02.kc, castV p (C11T02.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T02.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T02_rload_6]
    exact rank_castV_ne_zero_of_fst p ((3391572296869121202111865280724867708815855357021 / 3426793831761318384959429683271737419060419437950), (-256337449464092121877671051100641355269307605256397 / 82243051962271641239026312398521698057450066510800)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T02.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T02_large_integral
#print axioms C11T02_reduced_loads_nonzero

theorem C11T03_small_kills : C11T03.kr.card ≤ 1 ∧ C11T03.kc.card ≤ 1 := by decide +kernel

theorem C11T03_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T03.Integral p := by
  apply C11T03_integral p
  intro hd
  have hpos : 0 < C11T03_den := by decide +kernel
  have hbound : C11T03_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T03_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T03.kr, castV p (C11T03.rload d) ≠ 0) ∧
    (∀ d ∈ C11T03.kc, castV p (C11T03.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T03.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T03.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T03_cload_6]
    exact rank_castV_ne_zero_of_fst p ((3391572296869121202111865280724867708815855357021 / 3426793831761318384959429683271737419060419437950), (-256337449464092121877671051100641355269307605256397 / 82243051962271641239026312398521698057450066510800)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T03_large_integral
#print axioms C11T03_reduced_loads_nonzero

theorem C11T04_small_kills : C11T04.kr.card ≤ 1 ∧ C11T04.kc.card ≤ 1 := by decide +kernel

theorem C11T04_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T04.Integral p := by
  apply C11T04_integral p
  intro hd
  have hpos : 0 < C11T04_den := by decide +kernel
  have hbound : C11T04_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T04_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T04.kr, castV p (C11T04.rload d) ≠ 0) ∧
    (∀ d ∈ C11T04.kc, castV p (C11T04.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T04.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T04.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T04_large_integral
#print axioms C11T04_reduced_loads_nonzero

theorem C11T05_small_kills : C11T05.kr.card ≤ 1 ∧ C11T05.kc.card ≤ 1 := by decide +kernel

theorem C11T05_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T05.Integral p := by
  apply C11T05_integral p
  intro hd
  have hpos : 0 < C11T05_den := by decide +kernel
  have hbound : C11T05_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T05_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T05.kr, castV p (C11T05.rload d) ≠ 0) ∧
    (∀ d ∈ C11T05.kc, castV p (C11T05.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T05.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T05.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T05_cload_5]
    exact rank_castV_ne_zero_of_fst p ((1859424937291948945448943332369863 / 1880807400945288216403072781720000), (-10564709708391898345922033865398593 / 3385453321701518789525531007096000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T05_large_integral
#print axioms C11T05_reduced_loads_nonzero

theorem C11T06_small_kills : C11T06.kr.card ≤ 1 ∧ C11T06.kc.card ≤ 1 := by decide +kernel

theorem C11T06_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T06.Integral p := by
  apply C11T06_integral p
  intro hd
  have hpos : 0 < C11T06_den := by decide +kernel
  have hbound : C11T06_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T06_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T06.kr, castV p (C11T06.rload d) ≠ 0) ∧
    (∀ d ∈ C11T06.kc, castV p (C11T06.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T06.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T06_rload_5]
    exact rank_castV_ne_zero_of_fst p ((1859424937291948945448943332369863 / 1880807400945288216403072781720000), (-10564709708391898345922033865398593 / 3385453321701518789525531007096000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T06.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T06_large_integral
#print axioms C11T06_reduced_loads_nonzero

theorem C11T07_small_kills : C11T07.kr.card ≤ 1 ∧ C11T07.kc.card ≤ 1 := by decide +kernel

theorem C11T07_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T07.Integral p := by
  apply C11T07_integral p
  intro hd
  have hpos : 0 < C11T07_den := by decide +kernel
  have hbound : C11T07_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T07_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T07.kr, castV p (C11T07.rload d) ≠ 0) ∧
    (∀ d ∈ C11T07.kc, castV p (C11T07.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T07.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T07.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T07_large_integral
#print axioms C11T07_reduced_loads_nonzero

theorem C11T08_small_kills : C11T08.kr.card ≤ 1 ∧ C11T08.kc.card ≤ 1 := by decide +kernel

theorem C11T08_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T08.Integral p := by
  apply C11T08_integral p
  intro hd
  have hpos : 0 < C11T08_den := by decide +kernel
  have hbound : C11T08_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T08_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T08.kr, castV p (C11T08.rload d) ≠ 0) ∧
    (∀ d ∈ C11T08.kc, castV p (C11T08.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T08.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T08.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T08_cload_5]
    exact rank_castV_ne_zero_of_fst p ((-370553074216486997507 / 5506836616857338452000), (-81022178907268443019613 / 39649223641372836854400)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T08_large_integral
#print axioms C11T08_reduced_loads_nonzero

theorem C11T09_small_kills : C11T09.kr.card ≤ 1 ∧ C11T09.kc.card ≤ 1 := by decide +kernel

theorem C11T09_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T09.Integral p := by
  apply C11T09_integral p
  intro hd
  have hpos : 0 < C11T09_den := by decide +kernel
  have hbound : C11T09_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T09_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T09.kr, castV p (C11T09.rload d) ≠ 0) ∧
    (∀ d ∈ C11T09.kc, castV p (C11T09.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T09.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T09_rload_5]
    exact rank_castV_ne_zero_of_fst p ((-370553074216486997507 / 5506836616857338452000), (-81022178907268443019613 / 39649223641372836854400)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T09.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T09_large_integral
#print axioms C11T09_reduced_loads_nonzero

theorem C11T10_small_kills : C11T10.kr.card ≤ 1 ∧ C11T10.kc.card ≤ 1 := by decide +kernel

theorem C11T10_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T10.Integral p := by
  apply C11T10_integral p
  intro hd
  have hpos : 0 < C11T10_den := by decide +kernel
  have hbound : C11T10_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T10_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T10.kr, castV p (C11T10.rload d) ≠ 0) ∧
    (∀ d ∈ C11T10.kc, castV p (C11T10.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T10.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T10.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T10_large_integral
#print axioms C11T10_reduced_loads_nonzero

theorem C11T11_small_kills : C11T11.kr.card ≤ 1 ∧ C11T11.kc.card ≤ 1 := by decide +kernel

theorem C11T11_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T11.Integral p := by
  apply C11T11_integral p
  intro hd
  have hpos : 0 < C11T11_den := by decide +kernel
  have hbound : C11T11_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T11_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T11.kr, castV p (C11T11.rload d) ≠ 0) ∧
    (∀ d ∈ C11T11.kc, castV p (C11T11.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T11.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T11_rload_4]
    exact rank_castV_ne_zero_of_fst p ((194367277593143842371 / 196874370936942623680), (-1108000516289251149401 / 354373867686496722624)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T11.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T11_large_integral
#print axioms C11T11_reduced_loads_nonzero

theorem C11T12_small_kills : C11T12.kr.card ≤ 1 ∧ C11T12.kc.card ≤ 1 := by decide +kernel

theorem C11T12_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T12.Integral p := by
  apply C11T12_integral p
  intro hd
  have hpos : 0 < C11T12_den := by decide +kernel
  have hbound : C11T12_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T12_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T12.kr, castV p (C11T12.rload d) ≠ 0) ∧
    (∀ d ∈ C11T12.kc, castV p (C11T12.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T12.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T12.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T12_cload_4]
    exact rank_castV_ne_zero_of_fst p ((194367277593143842371 / 196874370936942623680), (-1108000516289251149401 / 354373867686496722624)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T12_large_integral
#print axioms C11T12_reduced_loads_nonzero

theorem C11T13_small_kills : C11T13.kr.card ≤ 1 ∧ C11T13.kc.card ≤ 1 := by decide +kernel

theorem C11T13_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T13.Integral p := by
  apply C11T13_integral p
  intro hd
  have hpos : 0 < C11T13_den := by decide +kernel
  have hbound : C11T13_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T13_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T13.kr, castV p (C11T13.rload d) ≠ 0) ∧
    (∀ d ∈ C11T13.kc, castV p (C11T13.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T13.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T13.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T13_large_integral
#print axioms C11T13_reduced_loads_nonzero

theorem C11T14_small_kills : C11T14.kr.card ≤ 1 ∧ C11T14.kc.card ≤ 1 := by decide +kernel

theorem C11T14_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T14.Integral p := by
  apply C11T14_integral p
  intro hd
  have hpos : 0 < C11T14_den := by decide +kernel
  have hbound : C11T14_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T14_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T14.kr, castV p (C11T14.rload d) ≠ 0) ∧
    (∀ d ∈ C11T14.kc, castV p (C11T14.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T14.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T14_rload_4]
    exact rank_castV_ne_zero_of_fst p ((-408997458901 / 1209399735600), (-918039340807 / 483759894240)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T14.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T14_large_integral
#print axioms C11T14_reduced_loads_nonzero

theorem C11T15_small_kills : C11T15.kr.card ≤ 1 ∧ C11T15.kc.card ≤ 1 := by decide +kernel

theorem C11T15_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T15.Integral p := by
  apply C11T15_integral p
  intro hd
  have hpos : 0 < C11T15_den := by decide +kernel
  have hbound : C11T15_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T15_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T15.kr, castV p (C11T15.rload d) ≠ 0) ∧
    (∀ d ∈ C11T15.kc, castV p (C11T15.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T15.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T15.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T15_cload_4]
    exact rank_castV_ne_zero_of_fst p ((-408997458901 / 1209399735600), (-918039340807 / 483759894240)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T15_large_integral
#print axioms C11T15_reduced_loads_nonzero

theorem C11T16_small_kills : C11T16.kr.card ≤ 1 ∧ C11T16.kc.card ≤ 1 := by decide +kernel

theorem C11T16_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T16.Integral p := by
  apply C11T16_integral p
  intro hd
  have hpos : 0 < C11T16_den := by decide +kernel
  have hbound : C11T16_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T16_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T16.kr, castV p (C11T16.rload d) ≠ 0) ∧
    (∀ d ∈ C11T16.kc, castV p (C11T16.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T16.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T16.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T16_large_integral
#print axioms C11T16_reduced_loads_nonzero

theorem C11T17_small_kills : C11T17.kr.card ≤ 1 ∧ C11T17.kc.card ≤ 1 := by decide +kernel

theorem C11T17_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T17.Integral p := by
  apply C11T17_integral p
  intro hd
  have hpos : 0 < C11T17_den := by decide +kernel
  have hbound : C11T17_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T17_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T17.kr, castV p (C11T17.rload d) ≠ 0) ∧
    (∀ d ∈ C11T17.kc, castV p (C11T17.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T17.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T17.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T17_cload_3]
    exact rank_castV_ne_zero_of_fst p ((2252922613519 / 2285991611352), (-7171489661615 / 2285991611352)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T17_large_integral
#print axioms C11T17_reduced_loads_nonzero

theorem C11T18_small_kills : C11T18.kr.card ≤ 1 ∧ C11T18.kc.card ≤ 1 := by decide +kernel

theorem C11T18_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T18.Integral p := by
  apply C11T18_integral p
  intro hd
  have hpos : 0 < C11T18_den := by decide +kernel
  have hbound : C11T18_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T18_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T18.kr, castV p (C11T18.rload d) ≠ 0) ∧
    (∀ d ∈ C11T18.kc, castV p (C11T18.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T18.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T18_rload_3]
    exact rank_castV_ne_zero_of_fst p ((2252922613519 / 2285991611352), (-7171489661615 / 2285991611352)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T18.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T18_large_integral
#print axioms C11T18_reduced_loads_nonzero

theorem C11T19_small_kills : C11T19.kr.card ≤ 1 ∧ C11T19.kc.card ≤ 1 := by decide +kernel

theorem C11T19_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T19.Integral p := by
  apply C11T19_integral p
  intro hd
  have hpos : 0 < C11T19_den := by decide +kernel
  have hbound : C11T19_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T19_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T19.kr, castV p (C11T19.rload d) ≠ 0) ∧
    (∀ d ∈ C11T19.kc, castV p (C11T19.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T19.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T19.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T19_large_integral
#print axioms C11T19_reduced_loads_nonzero

theorem C11T20_small_kills : C11T20.kr.card ≤ 1 ∧ C11T20.kc.card ≤ 1 := by decide +kernel

theorem C11T20_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T20.Integral p := by
  apply C11T20_integral p
  intro hd
  have hpos : 0 < C11T20_den := by decide +kernel
  have hbound : C11T20_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T20_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T20.kr, castV p (C11T20.rload d) ≠ 0) ∧
    (∀ d ∈ C11T20.kc, castV p (C11T20.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T20.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T20.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T20_large_integral
#print axioms C11T20_reduced_loads_nonzero

theorem C11T21_small_kills : C11T21.kr.card ≤ 1 ∧ C11T21.kc.card ≤ 1 := by decide +kernel

theorem C11T21_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T21.Integral p := by
  apply C11T21_integral p
  intro hd
  have hpos : 0 < C11T21_den := by decide +kernel
  have hbound : C11T21_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T21_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T21.kr, castV p (C11T21.rload d) ≠ 0) ∧
    (∀ d ∈ C11T21.kc, castV p (C11T21.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T21.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T21.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T21_cload_3]
    exact rank_castV_ne_zero_of_fst p ((-180101 / 215352), (-364955 / 215352)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T21_large_integral
#print axioms C11T21_reduced_loads_nonzero

theorem C11T22_small_kills : C11T22.kr.card ≤ 1 ∧ C11T22.kc.card ≤ 1 := by decide +kernel

theorem C11T22_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T22.Integral p := by
  apply C11T22_integral p
  intro hd
  have hpos : 0 < C11T22_den := by decide +kernel
  have hbound : C11T22_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T22_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T22.kr, castV p (C11T22.rload d) ≠ 0) ∧
    (∀ d ∈ C11T22.kc, castV p (C11T22.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T22.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T22_rload_3]
    exact rank_castV_ne_zero_of_fst p ((-180101 / 215352), (-364955 / 215352)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T22.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T22_large_integral
#print axioms C11T22_reduced_loads_nonzero

theorem C11T23_small_kills : C11T23.kr.card ≤ 1 ∧ C11T23.kc.card ≤ 1 := by decide +kernel

theorem C11T23_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T23.Integral p := by
  apply C11T23_integral p
  intro hd
  have hpos : 0 < C11T23_den := by decide +kernel
  have hbound : C11T23_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T23_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T23.kr, castV p (C11T23.rload d) ≠ 0) ∧
    (∀ d ∈ C11T23.kc, castV p (C11T23.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T23.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T23_rload_2]
    exact rank_castV_ne_zero_of_fst p ((2664353 / 2709288), (-950765 / 301032)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T23.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T23_large_integral
#print axioms C11T23_reduced_loads_nonzero

theorem C11T24_small_kills : C11T24.kr.card ≤ 1 ∧ C11T24.kc.card ≤ 1 := by decide +kernel

theorem C11T24_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T24.Integral p := by
  apply C11T24_integral p
  intro hd
  have hpos : 0 < C11T24_den := by decide +kernel
  have hbound : C11T24_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T24_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T24.kr, castV p (C11T24.rload d) ≠ 0) ∧
    (∀ d ∈ C11T24.kc, castV p (C11T24.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T24.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T24.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T24_cload_2]
    exact rank_castV_ne_zero_of_fst p ((2664353 / 2709288), (-950765 / 301032)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T24_large_integral
#print axioms C11T24_reduced_loads_nonzero

theorem C11T25_small_kills : C11T25.kr.card ≤ 1 ∧ C11T25.kc.card ≤ 1 := by decide +kernel

theorem C11T25_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T25.Integral p := by
  apply C11T25_integral p
  intro hd
  have hpos : 0 < C11T25_den := by decide +kernel
  have hbound : C11T25_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T25_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T25.kr, castV p (C11T25.rload d) ≠ 0) ∧
    (∀ d ∈ C11T25.kc, castV p (C11T25.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T25.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T25.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T25_large_integral
#print axioms C11T25_reduced_loads_nonzero

theorem C11T26_small_kills : C11T26.kr.card ≤ 1 ∧ C11T26.kc.card ≤ 1 := by decide +kernel

theorem C11T26_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T26.Integral p := by
  apply C11T26_integral p
  intro hd
  have hpos : 0 < C11T26_den := by decide +kernel
  have hbound : C11T26_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T26_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T26.kr, castV p (C11T26.rload d) ≠ 0) ∧
    (∀ d ∈ C11T26.kc, castV p (C11T26.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T26.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T26.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T26_large_integral
#print axioms C11T26_reduced_loads_nonzero

theorem C11T27_small_kills : C11T27.kr.card ≤ 1 ∧ C11T27.kc.card ≤ 1 := by decide +kernel

theorem C11T27_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T27.Integral p := by
  apply C11T27_integral p
  intro hd
  have hpos : 0 < C11T27_den := by decide +kernel
  have hbound : C11T27_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T27_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T27.kr, castV p (C11T27.rload d) ≠ 0) ∧
    (∀ d ∈ C11T27.kc, castV p (C11T27.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T27.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T27_rload_2]
    exact rank_castV_ne_zero_of_fst p ((-13 / 6), (-25 / 18)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T27.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T27_large_integral
#print axioms C11T27_reduced_loads_nonzero

theorem C11T28_small_kills : C11T28.kr.card ≤ 1 ∧ C11T28.kc.card ≤ 1 := by decide +kernel

theorem C11T28_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T28.Integral p := by
  apply C11T28_integral p
  intro hd
  have hpos : 0 < C11T28_den := by decide +kernel
  have hbound : C11T28_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T28_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T28.kr, castV p (C11T28.rload d) ≠ 0) ∧
    (∀ d ∈ C11T28.kc, castV p (C11T28.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T28.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T28.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T28_cload_2]
    exact rank_castV_ne_zero_of_fst p ((-13 / 6), (-25 / 18)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T28_large_integral
#print axioms C11T28_reduced_loads_nonzero

theorem C11T29_small_kills : C11T29.kr.card ≤ 1 ∧ C11T29.kc.card ≤ 1 := by decide +kernel

theorem C11T29_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T29.Integral p := by
  apply C11T29_integral p
  intro hd
  have hpos : 0 < C11T29_den := by decide +kernel
  have hbound : C11T29_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T29_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T29.kr, castV p (C11T29.rload d) ≠ 0) ∧
    (∀ d ∈ C11T29.kc, castV p (C11T29.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T29.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T29.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T29_cload_1]
    exact rank_castV_ne_zero_of_fst p ((433 / 441), (-45 / 14)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T29_large_integral
#print axioms C11T29_reduced_loads_nonzero

theorem C11T30_small_kills : C11T30.kr.card ≤ 1 ∧ C11T30.kc.card ≤ 1 := by decide +kernel

theorem C11T30_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T30.Integral p := by
  apply C11T30_integral p
  intro hd
  have hpos : 0 < C11T30_den := by decide +kernel
  have hbound : C11T30_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T30_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T30.kr, castV p (C11T30.rload d) ≠ 0) ∧
    (∀ d ∈ C11T30.kc, castV p (C11T30.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T30.kr = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T30_rload_1]
    exact rank_castV_ne_zero_of_fst p ((433 / 441), (-45 / 14)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T30.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T30_large_integral
#print axioms C11T30_reduced_loads_nonzero

theorem C11T31_small_kills : C11T31.kr.card ≤ 1 ∧ C11T31.kc.card ≤ 1 := by decide +kernel

theorem C11T31_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T31.Integral p := by
  apply C11T31_integral p
  intro hd
  have hpos : 0 < C11T31_den := by decide +kernel
  have hbound : C11T31_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T31_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T31.kr, castV p (C11T31.rload d) ≠ 0) ∧
    (∀ d ∈ C11T31.kc, castV p (C11T31.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T31.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T31.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T31_large_integral
#print axioms C11T31_reduced_loads_nonzero

theorem C11T32_small_kills : C11T32.kr.card ≤ 1 ∧ C11T32.kc.card ≤ 1 := by decide +kernel

theorem C11T32_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T32.Integral p := by
  apply C11T32_integral p
  intro hd
  have hpos : 0 < C11T32_den := by decide +kernel
  have hbound : C11T32_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T32_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T32.kr, castV p (C11T32.rload d) ≠ 0) ∧
    (∀ d ∈ C11T32.kc, castV p (C11T32.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T32.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T32.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T32_large_integral
#print axioms C11T32_reduced_loads_nonzero

theorem C11T33_small_kills : C11T33.kr.card ≤ 1 ∧ C11T33.kc.card ≤ 1 := by decide +kernel

theorem C11T33_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T33.Integral p := by
  apply C11T33_integral p
  intro hd
  have hpos : 0 < C11T33_den := by decide +kernel
  have hbound : C11T33_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T33_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T33.kr, castV p (C11T33.rload d) ≠ 0) ∧
    (∀ d ∈ C11T33.kc, castV p (C11T33.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T33.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T33.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T33_cload_1]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T33_large_integral
#print axioms C11T33_reduced_loads_nonzero

theorem C11T34_small_kills : C11T34.kr.card ≤ 1 ∧ C11T34.kc.card ≤ 1 := by decide +kernel

theorem C11T34_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T34.Integral p := by
  apply C11T34_integral p
  intro hd
  have hpos : 0 < C11T34_den := by decide +kernel
  have hbound : C11T34_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T34_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T34.kr, castV p (C11T34.rload d) ≠ 0) ∧
    (∀ d ∈ C11T34.kc, castV p (C11T34.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T34.kr = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T34_rload_1]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T34.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T34_large_integral
#print axioms C11T34_reduced_loads_nonzero

theorem C11T35_small_kills : C11T35.kr.card ≤ 1 ∧ C11T35.kc.card ≤ 1 := by decide +kernel

theorem C11T35_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T35.Integral p := by
  apply C11T35_integral p
  intro hd
  have hpos : 0 < C11T35_den := by decide +kernel
  have hbound : C11T35_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T35_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T35.kr, castV p (C11T35.rload d) ≠ 0) ∧
    (∀ d ∈ C11T35.kc, castV p (C11T35.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T35.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T35_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T35.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T35_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T35_large_integral
#print axioms C11T35_reduced_loads_nonzero

theorem C11T36_small_kills : C11T36.kr.card ≤ 1 ∧ C11T36.kc.card ≤ 1 := by decide +kernel

theorem C11T36_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T36.Integral p := by
  apply C11T36_integral p
  intro hd
  have hpos : 0 < C11T36_den := by decide +kernel
  have hbound : C11T36_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T36_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T36.kr, castV p (C11T36.rload d) ≠ 0) ∧
    (∀ d ∈ C11T36.kc, castV p (C11T36.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T36.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T36_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (-7 / 2)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T36.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T36_large_integral
#print axioms C11T36_reduced_loads_nonzero

theorem C11T37_small_kills : C11T37.kr.card ≤ 1 ∧ C11T37.kc.card ≤ 1 := by decide +kernel

theorem C11T37_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T37.Integral p := by
  apply C11T37_integral p
  intro hd
  have hpos : 0 < C11T37_den := by decide +kernel
  have hbound : C11T37_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T37_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T37.kr, castV p (C11T37.rload d) ≠ 0) ∧
    (∀ d ∈ C11T37.kc, castV p (C11T37.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T37.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T37.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T37_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (-7 / 2)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T37_large_integral
#print axioms C11T37_reduced_loads_nonzero

theorem C11T38_small_kills : C11T38.kr.card ≤ 1 ∧ C11T38.kc.card ≤ 1 := by decide +kernel

theorem C11T38_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T38.Integral p := by
  apply C11T38_integral p
  intro hd
  have hpos : 0 < C11T38_den := by decide +kernel
  have hbound : C11T38_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T38_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T38.kr, castV p (C11T38.rload d) ≠ 0) ∧
    (∀ d ∈ C11T38.kc, castV p (C11T38.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T38.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T38_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C11T38.kc = ∅ := rfl
    simp [he] at hd

#print axioms C11T38_large_integral
#print axioms C11T38_reduced_loads_nonzero

theorem C11T39_small_kills : C11T39.kr.card ≤ 1 ∧ C11T39.kc.card ≤ 1 := by decide +kernel

theorem C11T39_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C11T39.Integral p := by
  apply C11T39_integral p
  intro hd
  have hpos : 0 < C11T39_den := by decide +kernel
  have hbound : C11T39_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C11T39_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C11T39.kr, castV p (C11T39.rload d) ≠ 0) ∧
    (∀ d ∈ C11T39.kc, castV p (C11T39.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C11T39.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C11T39.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C11T39_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C11T39_large_integral
#print axioms C11T39_reduced_loads_nonzero

end CatalanCore.Uniform.Bank.Sevenths.RankLoads
