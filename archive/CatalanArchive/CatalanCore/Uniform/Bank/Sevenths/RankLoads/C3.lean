import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C3
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData
theorem C3T00_small_kills : C3T00.kr.card ≤ 1 ∧ C3T00.kc.card ≤ 1 := by decide +kernel

theorem C3T00_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T00.Integral p := by
  apply C3T00_integral p
  intro hd
  have hpos : 0 < C3T00_den := by decide +kernel
  have hbound : C3T00_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T00_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T00.kr, castV p (C3T00.rload d) ≠ 0) ∧
    (∀ d ∈ C3T00.kc, castV p (C3T00.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T00.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T00_rload_6]
    exact rank_castV_ne_zero_of_fst p ((294483208314490275358668570677837 / 1049681878820509310974159666501254), (-1369040334672791665210133746385199 / 3498939596068364369913865555004180)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T00.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T00_large_integral
#print axioms C3T00_reduced_loads_nonzero

theorem C3T01_small_kills : C3T01.kr.card ≤ 1 ∧ C3T01.kc.card ≤ 1 := by decide +kernel

theorem C3T01_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T01.Integral p := by
  apply C3T01_integral p
  intro hd
  have hpos : 0 < C3T01_den := by decide +kernel
  have hbound : C3T01_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T01_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T01.kr, castV p (C3T01.rload d) ≠ 0) ∧
    (∀ d ∈ C3T01.kc, castV p (C3T01.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T01.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T01.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T01_cload_6]
    exact rank_castV_ne_zero_of_fst p ((294483208314490275358668570677837 / 1049681878820509310974159666501254), (-1369040334672791665210133746385199 / 3498939596068364369913865555004180)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T01_large_integral
#print axioms C3T01_reduced_loads_nonzero

theorem C3T02_small_kills : C3T02.kr.card ≤ 1 ∧ C3T02.kc.card ≤ 1 := by decide +kernel

theorem C3T02_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T02.Integral p := by
  apply C3T02_integral p
  intro hd
  have hpos : 0 < C3T02_den := by decide +kernel
  have hbound : C3T02_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T02_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T02.kr, castV p (C3T02.rload d) ≠ 0) ∧
    (∀ d ∈ C3T02.kc, castV p (C3T02.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T02.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T02_rload_6]
    exact rank_castV_ne_zero_of_fst p ((10588418675440147362036875120874044948683321 / 11973520181454296166988045888204460106796502), (-3660975139320157735123990380212192425909199 / 6301852727081208508941076783265505319366580)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T02.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T02_large_integral
#print axioms C3T02_reduced_loads_nonzero

theorem C3T03_small_kills : C3T03.kr.card ≤ 1 ∧ C3T03.kc.card ≤ 1 := by decide +kernel

theorem C3T03_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T03.Integral p := by
  apply C3T03_integral p
  intro hd
  have hpos : 0 < C3T03_den := by decide +kernel
  have hbound : C3T03_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T03_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T03.kr, castV p (C3T03.rload d) ≠ 0) ∧
    (∀ d ∈ C3T03.kc, castV p (C3T03.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T03.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T03.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T03_cload_6]
    exact rank_castV_ne_zero_of_fst p ((10588418675440147362036875120874044948683321 / 11973520181454296166988045888204460106796502), (-3660975139320157735123990380212192425909199 / 6301852727081208508941076783265505319366580)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T03_large_integral
#print axioms C3T03_reduced_loads_nonzero

theorem C3T04_small_kills : C3T04.kr.card ≤ 1 ∧ C3T04.kc.card ≤ 1 := by decide +kernel

theorem C3T04_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T04.Integral p := by
  apply C3T04_integral p
  intro hd
  have hpos : 0 < C3T04_den := by decide +kernel
  have hbound : C3T04_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T04_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T04.kr, castV p (C3T04.rload d) ≠ 0) ∧
    (∀ d ∈ C3T04.kc, castV p (C3T04.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T04.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T04.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T04_large_integral
#print axioms C3T04_reduced_loads_nonzero

theorem C3T05_small_kills : C3T05.kr.card ≤ 1 ∧ C3T05.kc.card ≤ 1 := by decide +kernel

theorem C3T05_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T05.Integral p := by
  apply C3T05_integral p
  intro hd
  have hpos : 0 < C3T05_den := by decide +kernel
  have hbound : C3T05_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T05_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T05.kr, castV p (C3T05.rload d) ≠ 0) ∧
    (∀ d ∈ C3T05.kc, castV p (C3T05.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T05.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T05.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T05_cload_5]
    exact rank_castV_ne_zero_of_fst p ((203496165588974891691696208082477 / 233299340887025959804754923014874), (-1358574380542247014514767217895147 / 2332993408870259598047549230148740)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T05_large_integral
#print axioms C3T05_reduced_loads_nonzero

theorem C3T06_small_kills : C3T06.kr.card ≤ 1 ∧ C3T06.kc.card ≤ 1 := by decide +kernel

theorem C3T06_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T06.Integral p := by
  apply C3T06_integral p
  intro hd
  have hpos : 0 < C3T06_den := by decide +kernel
  have hbound : C3T06_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T06_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T06.kr, castV p (C3T06.rload d) ≠ 0) ∧
    (∀ d ∈ C3T06.kc, castV p (C3T06.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T06.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T06_rload_5]
    exact rank_castV_ne_zero_of_fst p ((203496165588974891691696208082477 / 233299340887025959804754923014874), (-1358574380542247014514767217895147 / 2332993408870259598047549230148740)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T06.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T06_large_integral
#print axioms C3T06_reduced_loads_nonzero

theorem C3T07_small_kills : C3T07.kr.card ≤ 1 ∧ C3T07.kc.card ≤ 1 := by decide +kernel

theorem C3T07_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T07.Integral p := by
  apply C3T07_integral p
  intro hd
  have hpos : 0 < C3T07_den := by decide +kernel
  have hbound : C3T07_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T07_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T07.kr, castV p (C3T07.rload d) ≠ 0) ∧
    (∀ d ∈ C3T07.kc, castV p (C3T07.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T07.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T07.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T07_large_integral
#print axioms C3T07_reduced_loads_nonzero

theorem C3T08_small_kills : C3T08.kr.card ≤ 1 ∧ C3T08.kc.card ≤ 1 := by decide +kernel

theorem C3T08_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T08.Integral p := by
  apply C3T08_integral p
  intro hd
  have hpos : 0 < C3T08_den := by decide +kernel
  have hbound : C3T08_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T08_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T08.kr, castV p (C3T08.rload d) ≠ 0) ∧
    (∀ d ∈ C3T08.kc, castV p (C3T08.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T08.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T08.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T08_cload_5]
    exact rank_castV_ne_zero_of_fst p ((193131983321318700128386 / 1236718077708539662968875), (-1402631172187181546136 / 3805286392949352809135)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T08_large_integral
#print axioms C3T08_reduced_loads_nonzero

theorem C3T09_small_kills : C3T09.kr.card ≤ 1 ∧ C3T09.kc.card ≤ 1 := by decide +kernel

theorem C3T09_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T09.Integral p := by
  apply C3T09_integral p
  intro hd
  have hpos : 0 < C3T09_den := by decide +kernel
  have hbound : C3T09_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T09_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T09.kr, castV p (C3T09.rload d) ≠ 0) ∧
    (∀ d ∈ C3T09.kc, castV p (C3T09.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T09.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T09_rload_5]
    exact rank_castV_ne_zero_of_fst p ((193131983321318700128386 / 1236718077708539662968875), (-1402631172187181546136 / 3805286392949352809135)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T09.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T09_large_integral
#print axioms C3T09_reduced_loads_nonzero

theorem C3T10_small_kills : C3T10.kr.card ≤ 1 ∧ C3T10.kc.card ≤ 1 := by decide +kernel

theorem C3T10_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T10.Integral p := by
  apply C3T10_integral p
  intro hd
  have hpos : 0 < C3T10_den := by decide +kernel
  have hbound : C3T10_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T10_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T10.kr, castV p (C3T10.rload d) ≠ 0) ∧
    (∀ d ∈ C3T10.kc, castV p (C3T10.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T10.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T10.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T10_large_integral
#print axioms C3T10_reduced_loads_nonzero

theorem C3T11_small_kills : C3T11.kr.card ≤ 1 ∧ C3T11.kc.card ≤ 1 := by decide +kernel

theorem C3T11_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T11.Integral p := by
  apply C3T11_integral p
  intro hd
  have hpos : 0 < C3T11_den := by decide +kernel
  have hbound : C3T11_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T11_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T11.kr, castV p (C3T11.rload d) ≠ 0) ∧
    (∀ d ∈ C3T11.kc, castV p (C3T11.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T11.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T11_rload_4]
    exact rank_castV_ne_zero_of_fst p ((729448406438597088315038 / 851095280668746469018663), (-2492489969965951326860766 / 4255476403343732345093315)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T11.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T11_large_integral
#print axioms C3T11_reduced_loads_nonzero

theorem C3T12_small_kills : C3T12.kr.card ≤ 1 ∧ C3T12.kc.card ≤ 1 := by decide +kernel

theorem C3T12_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T12.Integral p := by
  apply C3T12_integral p
  intro hd
  have hpos : 0 < C3T12_den := by decide +kernel
  have hbound : C3T12_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T12_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T12.kr, castV p (C3T12.rload d) ≠ 0) ∧
    (∀ d ∈ C3T12.kc, castV p (C3T12.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T12.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T12.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T12_cload_4]
    exact rank_castV_ne_zero_of_fst p ((729448406438597088315038 / 851095280668746469018663), (-2492489969965951326860766 / 4255476403343732345093315)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T12_large_integral
#print axioms C3T12_reduced_loads_nonzero

theorem C3T13_small_kills : C3T13.kr.card ≤ 1 ∧ C3T13.kc.card ≤ 1 := by decide +kernel

theorem C3T13_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T13.Integral p := by
  apply C3T13_integral p
  intro hd
  have hpos : 0 < C3T13_den := by decide +kernel
  have hbound : C3T13_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T13_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T13.kr, castV p (C3T13.rload d) ≠ 0) ∧
    (∀ d ∈ C3T13.kc, castV p (C3T13.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T13.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T13.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T13_large_integral
#print axioms C3T13_reduced_loads_nonzero

theorem C3T14_small_kills : C3T14.kr.card ≤ 1 ∧ C3T14.kc.card ≤ 1 := by decide +kernel

theorem C3T14_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T14.Integral p := by
  apply C3T14_integral p
  intro hd
  have hpos : 0 < C3T14_den := by decide +kernel
  have hbound : C3T14_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T14_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T14.kr, castV p (C3T14.rload d) ≠ 0) ∧
    (∀ d ∈ C3T14.kc, castV p (C3T14.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T14.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T14_rload_4]
    exact rank_castV_ne_zero_of_fst p ((-71134325929822 / 2082470422341855), (-141287501650532 / 416494084468371)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T14.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T14_large_integral
#print axioms C3T14_reduced_loads_nonzero

theorem C3T15_small_kills : C3T15.kr.card ≤ 1 ∧ C3T15.kc.card ≤ 1 := by decide +kernel

theorem C3T15_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T15.Integral p := by
  apply C3T15_integral p
  intro hd
  have hpos : 0 < C3T15_den := by decide +kernel
  have hbound : C3T15_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T15_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T15.kr, castV p (C3T15.rload d) ≠ 0) ∧
    (∀ d ∈ C3T15.kc, castV p (C3T15.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T15.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T15.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T15_cload_4]
    exact rank_castV_ne_zero_of_fst p ((-71134325929822 / 2082470422341855), (-141287501650532 / 416494084468371)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T15_large_integral
#print axioms C3T15_reduced_loads_nonzero

theorem C3T16_small_kills : C3T16.kr.card ≤ 1 ∧ C3T16.kc.card ≤ 1 := by decide +kernel

theorem C3T16_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T16.Integral p := by
  apply C3T16_integral p
  intro hd
  have hpos : 0 < C3T16_den := by decide +kernel
  have hbound : C3T16_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T16_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T16.kr, castV p (C3T16.rload d) ≠ 0) ∧
    (∀ d ∈ C3T16.kc, castV p (C3T16.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T16.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T16.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T16_large_integral
#print axioms C3T16_reduced_loads_nonzero

theorem C3T17_small_kills : C3T17.kr.card ≤ 1 ∧ C3T17.kc.card ≤ 1 := by decide +kernel

theorem C3T17_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T17.Integral p := by
  apply C3T17_integral p
  intro hd
  have hpos : 0 < C3T17_den := by decide +kernel
  have hbound : C3T17_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T17_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T17.kr, castV p (C3T17.rload d) ≠ 0) ∧
    (∀ d ∈ C3T17.kc, castV p (C3T17.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T17.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T17.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T17_large_integral
#print axioms C3T17_reduced_loads_nonzero

theorem C3T18_small_kills : C3T18.kr.card ≤ 1 ∧ C3T18.kc.card ≤ 1 := by decide +kernel

theorem C3T18_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T18.Integral p := by
  apply C3T18_integral p
  intro hd
  have hpos : 0 < C3T18_den := by decide +kernel
  have hbound : C3T18_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T18_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T18.kr, castV p (C3T18.rload d) ≠ 0) ∧
    (∀ d ∈ C3T18.kc, castV p (C3T18.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T18.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T18.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T18_cload_3]
    exact rank_castV_ne_zero_of_fst p ((788366909380156 / 941279830593531), (-11176789824092293 / 18825596611870620)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T18_large_integral
#print axioms C3T18_reduced_loads_nonzero

theorem C3T19_small_kills : C3T19.kr.card ≤ 1 ∧ C3T19.kc.card ≤ 1 := by decide +kernel

theorem C3T19_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T19.Integral p := by
  apply C3T19_integral p
  intro hd
  have hpos : 0 < C3T19_den := by decide +kernel
  have hbound : C3T19_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T19_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T19.kr, castV p (C3T19.rload d) ≠ 0) ∧
    (∀ d ∈ C3T19.kc, castV p (C3T19.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T19.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T19_rload_3]
    exact rank_castV_ne_zero_of_fst p ((788366909380156 / 941279830593531), (-11176789824092293 / 18825596611870620)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T19.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T19_large_integral
#print axioms C3T19_reduced_loads_nonzero

theorem C3T20_small_kills : C3T20.kr.card ≤ 1 ∧ C3T20.kc.card ≤ 1 := by decide +kernel

theorem C3T20_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T20.Integral p := by
  apply C3T20_integral p
  intro hd
  have hpos : 0 < C3T20_den := by decide +kernel
  have hbound : C3T20_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T20_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T20.kr, castV p (C3T20.rload d) ≠ 0) ∧
    (∀ d ∈ C3T20.kc, castV p (C3T20.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T20.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T20.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T20_cload_3]
    exact rank_castV_ne_zero_of_fst p ((-74006459 / 197174400), (-29514697 / 98587200)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T20_large_integral
#print axioms C3T20_reduced_loads_nonzero

theorem C3T21_small_kills : C3T21.kr.card ≤ 1 ∧ C3T21.kc.card ≤ 1 := by decide +kernel

theorem C3T21_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T21.Integral p := by
  apply C3T21_integral p
  intro hd
  have hpos : 0 < C3T21_den := by decide +kernel
  have hbound : C3T21_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T21_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T21.kr, castV p (C3T21.rload d) ≠ 0) ∧
    (∀ d ∈ C3T21.kc, castV p (C3T21.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T21.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T21_rload_3]
    exact rank_castV_ne_zero_of_fst p ((-74006459 / 197174400), (-29514697 / 98587200)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T21.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T21_large_integral
#print axioms C3T21_reduced_loads_nonzero

theorem C3T22_small_kills : C3T22.kr.card ≤ 1 ∧ C3T22.kc.card ≤ 1 := by decide +kernel

theorem C3T22_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T22.Integral p := by
  apply C3T22_integral p
  intro hd
  have hpos : 0 < C3T22_den := by decide +kernel
  have hbound : C3T22_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T22_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T22.kr, castV p (C3T22.rload d) ≠ 0) ∧
    (∀ d ∈ C3T22.kc, castV p (C3T22.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T22.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T22.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T22_large_integral
#print axioms C3T22_reduced_loads_nonzero

theorem C3T23_small_kills : C3T23.kr.card ≤ 1 ∧ C3T23.kc.card ≤ 1 := by decide +kernel

theorem C3T23_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T23.Integral p := by
  apply C3T23_integral p
  intro hd
  have hpos : 0 < C3T23_den := by decide +kernel
  have hbound : C3T23_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T23_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T23.kr, castV p (C3T23.rload d) ≠ 0) ∧
    (∀ d ∈ C3T23.kc, castV p (C3T23.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T23.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T23.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T23_large_integral
#print axioms C3T23_reduced_loads_nonzero

theorem C3T24_small_kills : C3T24.kr.card ≤ 1 ∧ C3T24.kc.card ≤ 1 := by decide +kernel

theorem C3T24_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T24.Integral p := by
  apply C3T24_integral p
  intro hd
  have hpos : 0 < C3T24_den := by decide +kernel
  have hbound : C3T24_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T24_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T24.kr, castV p (C3T24.rload d) ≠ 0) ∧
    (∀ d ∈ C3T24.kc, castV p (C3T24.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T24.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T24_rload_2]
    exact rank_castV_ne_zero_of_fst p ((79192639 / 97467264), (-6238601 / 10152840)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T24.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T24_large_integral
#print axioms C3T24_reduced_loads_nonzero

theorem C3T25_small_kills : C3T25.kr.card ≤ 1 ∧ C3T25.kc.card ≤ 1 := by decide +kernel

theorem C3T25_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T25.Integral p := by
  apply C3T25_integral p
  intro hd
  have hpos : 0 < C3T25_den := by decide +kernel
  have hbound : C3T25_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T25_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T25.kr, castV p (C3T25.rload d) ≠ 0) ∧
    (∀ d ∈ C3T25.kc, castV p (C3T25.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T25.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T25.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T25_cload_2]
    exact rank_castV_ne_zero_of_fst p ((79192639 / 97467264), (-6238601 / 10152840)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T25_large_integral
#print axioms C3T25_reduced_loads_nonzero

theorem C3T26_small_kills : C3T26.kr.card ≤ 1 ∧ C3T26.kc.card ≤ 1 := by decide +kernel

theorem C3T26_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T26.Integral p := by
  apply C3T26_integral p
  intro hd
  have hpos : 0 < C3T26_den := by decide +kernel
  have hbound : C3T26_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T26_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T26.kr, castV p (C3T26.rload d) ≠ 0) ∧
    (∀ d ∈ C3T26.kc, castV p (C3T26.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T26.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T26_rload_2]
    exact rank_castV_ne_zero_of_fst p ((-101 / 80), (-29 / 120)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T26.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T26_large_integral
#print axioms C3T26_reduced_loads_nonzero

theorem C3T27_small_kills : C3T27.kr.card ≤ 1 ∧ C3T27.kc.card ≤ 1 := by decide +kernel

theorem C3T27_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T27.Integral p := by
  apply C3T27_integral p
  intro hd
  have hpos : 0 < C3T27_den := by decide +kernel
  have hbound : C3T27_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T27_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T27.kr, castV p (C3T27.rload d) ≠ 0) ∧
    (∀ d ∈ C3T27.kc, castV p (C3T27.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T27.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T27.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T27_cload_2]
    exact rank_castV_ne_zero_of_fst p ((-101 / 80), (-29 / 120)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T27_large_integral
#print axioms C3T27_reduced_loads_nonzero

theorem C3T28_small_kills : C3T28.kr.card ≤ 1 ∧ C3T28.kc.card ≤ 1 := by decide +kernel

theorem C3T28_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T28.Integral p := by
  apply C3T28_integral p
  intro hd
  have hpos : 0 < C3T28_den := by decide +kernel
  have hbound : C3T28_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T28_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T28.kr, castV p (C3T28.rload d) ≠ 0) ∧
    (∀ d ∈ C3T28.kc, castV p (C3T28.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T28.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T28.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T28_large_integral
#print axioms C3T28_reduced_loads_nonzero

theorem C3T29_small_kills : C3T29.kr.card ≤ 1 ∧ C3T29.kc.card ≤ 1 := by decide +kernel

theorem C3T29_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T29.Integral p := by
  apply C3T29_integral p
  intro hd
  have hpos : 0 < C3T29_den := by decide +kernel
  have hbound : C3T29_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T29_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T29.kr, castV p (C3T29.rload d) ≠ 0) ∧
    (∀ d ∈ C3T29.kc, castV p (C3T29.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T29.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T29.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T29_large_integral
#print axioms C3T29_reduced_loads_nonzero

theorem C3T30_small_kills : C3T30.kr.card ≤ 1 ∧ C3T30.kc.card ≤ 1 := by decide +kernel

theorem C3T30_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T30.Integral p := by
  apply C3T30_integral p
  intro hd
  have hpos : 0 < C3T30_den := by decide +kernel
  have hbound : C3T30_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T30_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T30.kr, castV p (C3T30.rload d) ≠ 0) ∧
    (∀ d ∈ C3T30.kc, castV p (C3T30.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T30.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T30.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T30_cload_1]
    exact rank_castV_ne_zero_of_fst p ((463 / 588), (-24 / 35)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T30_large_integral
#print axioms C3T30_reduced_loads_nonzero

theorem C3T31_small_kills : C3T31.kr.card ≤ 1 ∧ C3T31.kc.card ≤ 1 := by decide +kernel

theorem C3T31_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T31.Integral p := by
  apply C3T31_integral p
  intro hd
  have hpos : 0 < C3T31_den := by decide +kernel
  have hbound : C3T31_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T31_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T31.kr, castV p (C3T31.rload d) ≠ 0) ∧
    (∀ d ∈ C3T31.kc, castV p (C3T31.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T31.kr = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T31_rload_1]
    exact rank_castV_ne_zero_of_fst p ((463 / 588), (-24 / 35)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T31.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T31_large_integral
#print axioms C3T31_reduced_loads_nonzero

theorem C3T32_small_kills : C3T32.kr.card ≤ 1 ∧ C3T32.kc.card ≤ 1 := by decide +kernel

theorem C3T32_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T32.Integral p := by
  apply C3T32_integral p
  intro hd
  have hpos : 0 < C3T32_den := by decide +kernel
  have hbound : C3T32_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T32_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T32.kr, castV p (C3T32.rload d) ≠ 0) ∧
    (∀ d ∈ C3T32.kc, castV p (C3T32.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T32.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T32.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T32_cload_1]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T32_large_integral
#print axioms C3T32_reduced_loads_nonzero

theorem C3T33_small_kills : C3T33.kr.card ≤ 1 ∧ C3T33.kc.card ≤ 1 := by decide +kernel

theorem C3T33_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T33.Integral p := by
  apply C3T33_integral p
  intro hd
  have hpos : 0 < C3T33_den := by decide +kernel
  have hbound : C3T33_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T33_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T33.kr, castV p (C3T33.rload d) ≠ 0) ∧
    (∀ d ∈ C3T33.kc, castV p (C3T33.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T33.kr = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T33_rload_1]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T33.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T33_large_integral
#print axioms C3T33_reduced_loads_nonzero

theorem C3T34_small_kills : C3T34.kr.card ≤ 1 ∧ C3T34.kc.card ≤ 1 := by decide +kernel

theorem C3T34_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T34.Integral p := by
  apply C3T34_integral p
  intro hd
  have hpos : 0 < C3T34_den := by decide +kernel
  have hbound : C3T34_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T34_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T34.kr, castV p (C3T34.rload d) ≠ 0) ∧
    (∀ d ∈ C3T34.kc, castV p (C3T34.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T34.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T34.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T34_large_integral
#print axioms C3T34_reduced_loads_nonzero

theorem C3T35_small_kills : C3T35.kr.card ≤ 1 ∧ C3T35.kc.card ≤ 1 := by decide +kernel

theorem C3T35_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T35.Integral p := by
  apply C3T35_integral p
  intro hd
  have hpos : 0 < C3T35_den := by decide +kernel
  have hbound : C3T35_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T35_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T35.kr, castV p (C3T35.rload d) ≠ 0) ∧
    (∀ d ∈ C3T35.kc, castV p (C3T35.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T35.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T35_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T35.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T35_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T35_large_integral
#print axioms C3T35_reduced_loads_nonzero

theorem C3T36_small_kills : C3T36.kr.card ≤ 1 ∧ C3T36.kc.card ≤ 1 := by decide +kernel

theorem C3T36_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T36.Integral p := by
  apply C3T36_integral p
  intro hd
  have hpos : 0 < C3T36_den := by decide +kernel
  have hbound : C3T36_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T36_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T36.kr, castV p (C3T36.rload d) ≠ 0) ∧
    (∀ d ∈ C3T36.kc, castV p (C3T36.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T36.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T36_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (-7 / 5)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T36.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T36_large_integral
#print axioms C3T36_reduced_loads_nonzero

theorem C3T37_small_kills : C3T37.kr.card ≤ 1 ∧ C3T37.kc.card ≤ 1 := by decide +kernel

theorem C3T37_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T37.Integral p := by
  apply C3T37_integral p
  intro hd
  have hpos : 0 < C3T37_den := by decide +kernel
  have hbound : C3T37_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T37_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T37.kr, castV p (C3T37.rload d) ≠ 0) ∧
    (∀ d ∈ C3T37.kc, castV p (C3T37.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T37.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T37.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T37_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (-7 / 5)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T37_large_integral
#print axioms C3T37_reduced_loads_nonzero

theorem C3T38_small_kills : C3T38.kr.card ≤ 1 ∧ C3T38.kc.card ≤ 1 := by decide +kernel

theorem C3T38_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T38.Integral p := by
  apply C3T38_integral p
  intro hd
  have hpos : 0 < C3T38_den := by decide +kernel
  have hbound : C3T38_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T38_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T38.kr, castV p (C3T38.rload d) ≠ 0) ∧
    (∀ d ∈ C3T38.kc, castV p (C3T38.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T38.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T38_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C3T38.kc = ∅ := rfl
    simp [he] at hd

#print axioms C3T38_large_integral
#print axioms C3T38_reduced_loads_nonzero

theorem C3T39_small_kills : C3T39.kr.card ≤ 1 ∧ C3T39.kc.card ≤ 1 := by decide +kernel

theorem C3T39_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C3T39.Integral p := by
  apply C3T39_integral p
  intro hd
  have hpos : 0 < C3T39_den := by decide +kernel
  have hbound : C3T39_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C3T39_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C3T39.kr, castV p (C3T39.rload d) ≠ 0) ∧
    (∀ d ∈ C3T39.kc, castV p (C3T39.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C3T39.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C3T39.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C3T39_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C3T39_large_integral
#print axioms C3T39_reduced_loads_nonzero

end CatalanCore.Uniform.Bank.Sevenths.RankLoads
