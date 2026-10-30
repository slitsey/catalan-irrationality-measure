import CatalanCore.Uniform.Bank.Sevenths.RankPalette.C9
import CatalanCore.Uniform.Bank.Sevenths.RankUnits
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths.RankLoads
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer RankData
theorem C9T00_small_kills : C9T00.kr.card ≤ 1 ∧ C9T00.kc.card ≤ 1 := by decide +kernel

theorem C9T00_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T00.Integral p := by
  apply C9T00_integral p
  intro hd
  have hpos : 0 < C9T00_den := by decide +kernel
  have hbound : C9T00_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T00_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T00.kr, castV p (C9T00.rload d) ≠ 0) ∧
    (∀ d ∈ C9T00.kc, castV p (C9T00.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T00.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T00_rload_6]
    exact rank_castV_ne_zero_of_fst p ((160698051091945740838900666066511451019 / 620970870051521735219250583759609371000), (-2640804646404584955300680491933381256041 / 3725825220309130411315503502557656226000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T00.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T00_large_integral
#print axioms C9T00_reduced_loads_nonzero

theorem C9T01_small_kills : C9T01.kr.card ≤ 1 ∧ C9T01.kc.card ≤ 1 := by decide +kernel

theorem C9T01_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T01.Integral p := by
  apply C9T01_integral p
  intro hd
  have hpos : 0 < C9T01_den := by decide +kernel
  have hbound : C9T01_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T01_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T01.kr, castV p (C9T01.rload d) ≠ 0) ∧
    (∀ d ∈ C9T01.kc, castV p (C9T01.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T01.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T01.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T01_cload_6]
    exact rank_castV_ne_zero_of_fst p ((160698051091945740838900666066511451019 / 620970870051521735219250583759609371000), (-2640804646404584955300680491933381256041 / 3725825220309130411315503502557656226000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T01_large_integral
#print axioms C9T01_reduced_loads_nonzero

theorem C9T02_small_kills : C9T02.kr.card ≤ 1 ∧ C9T02.kc.card ≤ 1 := by decide +kernel

theorem C9T02_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T02.Integral p := by
  apply C9T02_integral p
  intro hd
  have hpos : 0 < C9T02_den := by decide +kernel
  have hbound : C9T02_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T02_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T02.kr, castV p (C9T02.rload d) ≠ 0) ∧
    (∀ d ∈ C9T02.kc, castV p (C9T02.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T02.kr = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T02_rload_6]
    exact rank_castV_ne_zero_of_fst p ((797245704292218020143124714204509304912334432342707 / 854850861404880227492362066261940112446375566083000), (-5413966266810456649582988012474527489847262950579873 / 5129105168429281364954172397571640674678253396498000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T02.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T02_large_integral
#print axioms C9T02_reduced_loads_nonzero

theorem C9T03_small_kills : C9T03.kr.card ≤ 1 ∧ C9T03.kc.card ≤ 1 := by decide +kernel

theorem C9T03_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T03.Integral p := by
  apply C9T03_integral p
  intro hd
  have hpos : 0 < C9T03_den := by decide +kernel
  have hbound : C9T03_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T03_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T03.kr, castV p (C9T03.rload d) ≠ 0) ∧
    (∀ d ∈ C9T03.kc, castV p (C9T03.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T03.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T03.kc = {6} := rfl
    have hde : d = 6 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T03_cload_6]
    exact rank_castV_ne_zero_of_fst p ((797245704292218020143124714204509304912334432342707 / 854850861404880227492362066261940112446375566083000), (-5413966266810456649582988012474527489847262950579873 / 5129105168429281364954172397571640674678253396498000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T03_large_integral
#print axioms C9T03_reduced_loads_nonzero

theorem C9T04_small_kills : C9T04.kr.card ≤ 1 ∧ C9T04.kc.card ≤ 1 := by decide +kernel

theorem C9T04_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T04.Integral p := by
  apply C9T04_integral p
  intro hd
  have hpos : 0 < C9T04_den := by decide +kernel
  have hbound : C9T04_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T04_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T04.kr, castV p (C9T04.rload d) ≠ 0) ∧
    (∀ d ∈ C9T04.kc, castV p (C9T04.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T04.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T04.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T04_large_integral
#print axioms C9T04_reduced_loads_nonzero

theorem C9T05_small_kills : C9T05.kr.card ≤ 1 ∧ C9T05.kc.card ≤ 1 := by decide +kernel

theorem C9T05_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T05.Integral p := by
  apply C9T05_integral p
  intro hd
  have hpos : 0 < C9T05_den := by decide +kernel
  have hbound : C9T05_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T05_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T05.kr, castV p (C9T05.rload d) ≠ 0) ∧
    (∀ d ∈ C9T05.kc, castV p (C9T05.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T05.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T05.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T05_cload_5]
    exact rank_castV_ne_zero_of_fst p ((749952733977325523646269837998889873 / 810189578445930845012869753666217000), (-15431064562369921674403797899409240821 / 14583412412026755210231655565991906000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T05_large_integral
#print axioms C9T05_reduced_loads_nonzero

theorem C9T06_small_kills : C9T06.kr.card ≤ 1 ∧ C9T06.kc.card ≤ 1 := by decide +kernel

theorem C9T06_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T06.Integral p := by
  apply C9T06_integral p
  intro hd
  have hpos : 0 < C9T06_den := by decide +kernel
  have hbound : C9T06_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T06_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T06.kr, castV p (C9T06.rload d) ≠ 0) ∧
    (∀ d ∈ C9T06.kc, castV p (C9T06.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T06.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T06_rload_5]
    exact rank_castV_ne_zero_of_fst p ((749952733977325523646269837998889873 / 810189578445930845012869753666217000), (-15431064562369921674403797899409240821 / 14583412412026755210231655565991906000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T06.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T06_large_integral
#print axioms C9T06_reduced_loads_nonzero

theorem C9T07_small_kills : C9T07.kr.card ≤ 1 ∧ C9T07.kc.card ≤ 1 := by decide +kernel

theorem C9T07_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T07.Integral p := by
  apply C9T07_integral p
  intro hd
  have hpos : 0 < C9T07_den := by decide +kernel
  have hbound : C9T07_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T07_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T07.kr, castV p (C9T07.rload d) ≠ 0) ∧
    (∀ d ∈ C9T07.kc, castV p (C9T07.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T07.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T07.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T07_large_integral
#print axioms C9T07_reduced_loads_nonzero

theorem C9T08_small_kills : C9T08.kr.card ≤ 1 ∧ C9T08.kc.card ≤ 1 := by decide +kernel

theorem C9T08_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T08.Integral p := by
  apply C9T08_integral p
  intro hd
  have hpos : 0 < C9T08_den := by decide +kernel
  have hbound : C9T08_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T08_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T08.kr, castV p (C9T08.rload d) ≠ 0) ∧
    (∀ d ∈ C9T08.kc, castV p (C9T08.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T08.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T08.kc = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T08_cload_5]
    exact rank_castV_ne_zero_of_fst p ((64595300400589858614263297 / 508723922290294453028913000), (-226912852446535843071198047 / 339149281526862968685942000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T08_large_integral
#print axioms C9T08_reduced_loads_nonzero

theorem C9T09_small_kills : C9T09.kr.card ≤ 1 ∧ C9T09.kc.card ≤ 1 := by decide +kernel

theorem C9T09_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T09.Integral p := by
  apply C9T09_integral p
  intro hd
  have hpos : 0 < C9T09_den := by decide +kernel
  have hbound : C9T09_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T09_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T09.kr, castV p (C9T09.rload d) ≠ 0) ∧
    (∀ d ∈ C9T09.kc, castV p (C9T09.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T09.kr = {5} := rfl
    have hde : d = 5 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T09_rload_5]
    exact rank_castV_ne_zero_of_fst p ((64595300400589858614263297 / 508723922290294453028913000), (-226912852446535843071198047 / 339149281526862968685942000)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T09.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T09_large_integral
#print axioms C9T09_reduced_loads_nonzero

theorem C9T10_small_kills : C9T10.kr.card ≤ 1 ∧ C9T10.kc.card ≤ 1 := by decide +kernel

theorem C9T10_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T10.Integral p := by
  apply C9T10_integral p
  intro hd
  have hpos : 0 < C9T10_den := by decide +kernel
  have hbound : C9T10_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T10_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T10.kr, castV p (C9T10.rload d) ≠ 0) ∧
    (∀ d ∈ C9T10.kc, castV p (C9T10.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T10.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T10.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T10_large_integral
#print axioms C9T10_reduced_loads_nonzero

theorem C9T11_small_kills : C9T11.kr.card ≤ 1 ∧ C9T11.kc.card ≤ 1 := by decide +kernel

theorem C9T11_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T11.Integral p := by
  apply C9T11_integral p
  intro hd
  have hpos : 0 < C9T11_den := by decide +kernel
  have hbound : C9T11_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T11_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T11.kr, castV p (C9T11.rload d) ≠ 0) ∧
    (∀ d ∈ C9T11.kc, castV p (C9T11.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T11.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T11_rload_4]
    exact rank_castV_ne_zero_of_fst p ((9451529343565843884853453 / 10307518079936754339016200), (-26568030354499583284849 / 24987922618028495367312)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T11.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T11_large_integral
#print axioms C9T11_reduced_loads_nonzero

theorem C9T12_small_kills : C9T12.kr.card ≤ 1 ∧ C9T12.kc.card ≤ 1 := by decide +kernel

theorem C9T12_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T12.Integral p := by
  apply C9T12_integral p
  intro hd
  have hpos : 0 < C9T12_den := by decide +kernel
  have hbound : C9T12_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T12_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T12.kr, castV p (C9T12.rload d) ≠ 0) ∧
    (∀ d ∈ C9T12.kc, castV p (C9T12.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T12.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T12.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T12_cload_4]
    exact rank_castV_ne_zero_of_fst p ((9451529343565843884853453 / 10307518079936754339016200), (-26568030354499583284849 / 24987922618028495367312)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T12_large_integral
#print axioms C9T12_reduced_loads_nonzero

theorem C9T13_small_kills : C9T13.kr.card ≤ 1 ∧ C9T13.kc.card ≤ 1 := by decide +kernel

theorem C9T13_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T13.Integral p := by
  apply C9T13_integral p
  intro hd
  have hpos : 0 < C9T13_den := by decide +kernel
  have hbound : C9T13_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T13_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T13.kr, castV p (C9T13.rload d) ≠ 0) ∧
    (∀ d ∈ C9T13.kc, castV p (C9T13.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T13.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T13.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T13_large_integral
#print axioms C9T13_reduced_loads_nonzero

theorem C9T14_small_kills : C9T14.kr.card ≤ 1 ∧ C9T14.kc.card ≤ 1 := by decide +kernel

theorem C9T14_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T14.Integral p := by
  apply C9T14_integral p
  intro hd
  have hpos : 0 < C9T14_den := by decide +kernel
  have hbound : C9T14_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T14_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T14.kr, castV p (C9T14.rload d) ≠ 0) ∧
    (∀ d ∈ C9T14.kc, castV p (C9T14.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T14.kr = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T14_rload_4]
    exact rank_castV_ne_zero_of_fst p ((-11868940030333 / 156622051398582), (-1611490998685361 / 2610367523309700)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T14.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T14_large_integral
#print axioms C9T14_reduced_loads_nonzero

theorem C9T15_small_kills : C9T15.kr.card ≤ 1 ∧ C9T15.kc.card ≤ 1 := by decide +kernel

theorem C9T15_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T15.Integral p := by
  apply C9T15_integral p
  intro hd
  have hpos : 0 < C9T15_den := by decide +kernel
  have hbound : C9T15_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T15_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T15.kr, castV p (C9T15.rload d) ≠ 0) ∧
    (∀ d ∈ C9T15.kc, castV p (C9T15.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T15.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T15.kc = {4} := rfl
    have hde : d = 4 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T15_cload_4]
    exact rank_castV_ne_zero_of_fst p ((-11868940030333 / 156622051398582), (-1611490998685361 / 2610367523309700)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T15_large_integral
#print axioms C9T15_reduced_loads_nonzero

theorem C9T16_small_kills : C9T16.kr.card ≤ 1 ∧ C9T16.kc.card ≤ 1 := by decide +kernel

theorem C9T16_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T16.Integral p := by
  apply C9T16_integral p
  intro hd
  have hpos : 0 < C9T16_den := by decide +kernel
  have hbound : C9T16_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T16_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T16.kr, castV p (C9T16.rload d) ≠ 0) ∧
    (∀ d ∈ C9T16.kc, castV p (C9T16.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T16.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T16.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T16_large_integral
#print axioms C9T16_reduced_loads_nonzero

theorem C9T17_small_kills : C9T17.kr.card ≤ 1 ∧ C9T17.kc.card ≤ 1 := by decide +kernel

theorem C9T17_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T17.Integral p := by
  apply C9T17_integral p
  intro hd
  have hpos : 0 < C9T17_den := by decide +kernel
  have hbound : C9T17_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T17_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T17.kr, castV p (C9T17.rload d) ≠ 0) ∧
    (∀ d ∈ C9T17.kc, castV p (C9T17.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T17.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T17.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T17_cload_3]
    exact rank_castV_ne_zero_of_fst p ((2530966133977 / 2793743456625), (-300024842874739 / 279374345662500)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T17_large_integral
#print axioms C9T17_reduced_loads_nonzero

theorem C9T18_small_kills : C9T18.kr.card ≤ 1 ∧ C9T18.kc.card ≤ 1 := by decide +kernel

theorem C9T18_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T18.Integral p := by
  apply C9T18_integral p
  intro hd
  have hpos : 0 < C9T18_den := by decide +kernel
  have hbound : C9T18_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T18_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T18.kr, castV p (C9T18.rload d) ≠ 0) ∧
    (∀ d ∈ C9T18.kc, castV p (C9T18.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T18.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T18_rload_3]
    exact rank_castV_ne_zero_of_fst p ((2530966133977 / 2793743456625), (-300024842874739 / 279374345662500)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T18.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T18_large_integral
#print axioms C9T18_reduced_loads_nonzero

theorem C9T19_small_kills : C9T19.kr.card ≤ 1 ∧ C9T19.kc.card ≤ 1 := by decide +kernel

theorem C9T19_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T19.Integral p := by
  apply C9T19_integral p
  intro hd
  have hpos : 0 < C9T19_den := by decide +kernel
  have hbound : C9T19_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T19_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T19.kr, castV p (C9T19.rload d) ≠ 0) ∧
    (∀ d ∈ C9T19.kc, castV p (C9T19.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T19.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T19.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T19_large_integral
#print axioms C9T19_reduced_loads_nonzero

theorem C9T20_small_kills : C9T20.kr.card ≤ 1 ∧ C9T20.kc.card ≤ 1 := by decide +kernel

theorem C9T20_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T20.Integral p := by
  apply C9T20_integral p
  intro hd
  have hpos : 0 < C9T20_den := by decide +kernel
  have hbound : C9T20_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T20_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T20.kr, castV p (C9T20.rload d) ≠ 0) ∧
    (∀ d ∈ C9T20.kc, castV p (C9T20.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T20.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T20.kc = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T20_cload_3]
    exact rank_castV_ne_zero_of_fst p ((-1048666 / 2375703), (-5194703 / 9502812)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T20_large_integral
#print axioms C9T20_reduced_loads_nonzero

theorem C9T21_small_kills : C9T21.kr.card ≤ 1 ∧ C9T21.kc.card ≤ 1 := by decide +kernel

theorem C9T21_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T21.Integral p := by
  apply C9T21_integral p
  intro hd
  have hpos : 0 < C9T21_den := by decide +kernel
  have hbound : C9T21_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T21_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T21.kr, castV p (C9T21.rload d) ≠ 0) ∧
    (∀ d ∈ C9T21.kc, castV p (C9T21.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T21.kr = {3} := rfl
    have hde : d = 3 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T21_rload_3]
    exact rank_castV_ne_zero_of_fst p ((-1048666 / 2375703), (-5194703 / 9502812)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T21.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T21_large_integral
#print axioms C9T21_reduced_loads_nonzero

theorem C9T22_small_kills : C9T22.kr.card ≤ 1 ∧ C9T22.kc.card ≤ 1 := by decide +kernel

theorem C9T22_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T22.Integral p := by
  apply C9T22_integral p
  intro hd
  have hpos : 0 < C9T22_den := by decide +kernel
  have hbound : C9T22_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T22_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T22.kr, castV p (C9T22.rload d) ≠ 0) ∧
    (∀ d ∈ C9T22.kc, castV p (C9T22.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T22.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T22.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T22_large_integral
#print axioms C9T22_reduced_loads_nonzero

theorem C9T23_small_kills : C9T23.kr.card ≤ 1 ∧ C9T23.kc.card ≤ 1 := by decide +kernel

theorem C9T23_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T23.Integral p := by
  apply C9T23_integral p
  intro hd
  have hpos : 0 < C9T23_den := by decide +kernel
  have hbound : C9T23_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T23_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T23.kr, castV p (C9T23.rload d) ≠ 0) ∧
    (∀ d ∈ C9T23.kc, castV p (C9T23.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T23.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T23.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T23_large_integral
#print axioms C9T23_reduced_loads_nonzero

theorem C9T24_small_kills : C9T24.kr.card ≤ 1 ∧ C9T24.kc.card ≤ 1 := by decide +kernel

theorem C9T24_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T24.Integral p := by
  apply C9T24_integral p
  intro hd
  have hpos : 0 < C9T24_den := by decide +kernel
  have hbound : C9T24_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T24_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T24.kr, castV p (C9T24.rload d) ≠ 0) ∧
    (∀ d ∈ C9T24.kc, castV p (C9T24.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T24.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T24_rload_2]
    exact rank_castV_ne_zero_of_fst p ((6772225 / 7589241), (-1011251 / 919908)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T24.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T24_large_integral
#print axioms C9T24_reduced_loads_nonzero

theorem C9T25_small_kills : C9T25.kr.card ≤ 1 ∧ C9T25.kc.card ≤ 1 := by decide +kernel

theorem C9T25_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T25.Integral p := by
  apply C9T25_integral p
  intro hd
  have hpos : 0 < C9T25_den := by decide +kernel
  have hbound : C9T25_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T25_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T25.kr, castV p (C9T25.rload d) ≠ 0) ∧
    (∀ d ∈ C9T25.kc, castV p (C9T25.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T25.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T25.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T25_cload_2]
    exact rank_castV_ne_zero_of_fst p ((6772225 / 7589241), (-1011251 / 919908)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T25_large_integral
#print axioms C9T25_reduced_loads_nonzero

theorem C9T26_small_kills : C9T26.kr.card ≤ 1 ∧ C9T26.kc.card ≤ 1 := by decide +kernel

theorem C9T26_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T26.Integral p := by
  apply C9T26_integral p
  intro hd
  have hpos : 0 < C9T26_den := by decide +kernel
  have hbound : C9T26_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T26_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T26.kr, castV p (C9T26.rload d) ≠ 0) ∧
    (∀ d ∈ C9T26.kc, castV p (C9T26.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T26.kr = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T26_rload_2]
    exact rank_castV_ne_zero_of_fst p ((-123 / 88), (-39 / 88)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T26.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T26_large_integral
#print axioms C9T26_reduced_loads_nonzero

theorem C9T27_small_kills : C9T27.kr.card ≤ 1 ∧ C9T27.kc.card ≤ 1 := by decide +kernel

theorem C9T27_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T27.Integral p := by
  apply C9T27_integral p
  intro hd
  have hpos : 0 < C9T27_den := by decide +kernel
  have hbound : C9T27_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T27_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T27.kr, castV p (C9T27.rload d) ≠ 0) ∧
    (∀ d ∈ C9T27.kc, castV p (C9T27.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T27.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T27.kc = {2} := rfl
    have hde : d = 2 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T27_cload_2]
    exact rank_castV_ne_zero_of_fst p ((-123 / 88), (-39 / 88)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T27_large_integral
#print axioms C9T27_reduced_loads_nonzero

theorem C9T28_small_kills : C9T28.kr.card ≤ 1 ∧ C9T28.kc.card ≤ 1 := by decide +kernel

theorem C9T28_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T28.Integral p := by
  apply C9T28_integral p
  intro hd
  have hpos : 0 < C9T28_den := by decide +kernel
  have hbound : C9T28_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T28_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T28.kr, castV p (C9T28.rload d) ≠ 0) ∧
    (∀ d ∈ C9T28.kc, castV p (C9T28.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T28.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T28.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T28_large_integral
#print axioms C9T28_reduced_loads_nonzero

theorem C9T29_small_kills : C9T29.kr.card ≤ 1 ∧ C9T29.kc.card ≤ 1 := by decide +kernel

theorem C9T29_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T29.Integral p := by
  apply C9T29_integral p
  intro hd
  have hpos : 0 < C9T29_den := by decide +kernel
  have hbound : C9T29_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T29_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T29.kr, castV p (C9T29.rload d) ≠ 0) ∧
    (∀ d ∈ C9T29.kc, castV p (C9T29.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T29.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T29.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T29_large_integral
#print axioms C9T29_reduced_loads_nonzero

theorem C9T30_small_kills : C9T30.kr.card ≤ 1 ∧ C9T30.kc.card ≤ 1 := by decide +kernel

theorem C9T30_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T30.Integral p := by
  apply C9T30_integral p
  intro hd
  have hpos : 0 < C9T30_den := by decide +kernel
  have hbound : C9T30_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T30_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T30.kr, castV p (C9T30.rload d) ≠ 0) ∧
    (∀ d ∈ C9T30.kc, castV p (C9T30.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T30.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T30.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T30_cload_1]
    exact rank_castV_ne_zero_of_fst p ((475 / 539), (-33 / 28)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T30_large_integral
#print axioms C9T30_reduced_loads_nonzero

theorem C9T31_small_kills : C9T31.kr.card ≤ 1 ∧ C9T31.kc.card ≤ 1 := by decide +kernel

theorem C9T31_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T31.Integral p := by
  apply C9T31_integral p
  intro hd
  have hpos : 0 < C9T31_den := by decide +kernel
  have hbound : C9T31_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T31_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T31.kr, castV p (C9T31.rload d) ≠ 0) ∧
    (∀ d ∈ C9T31.kc, castV p (C9T31.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T31.kr = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T31_rload_1]
    exact rank_castV_ne_zero_of_fst p ((475 / 539), (-33 / 28)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T31.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T31_large_integral
#print axioms C9T31_reduced_loads_nonzero

theorem C9T32_small_kills : C9T32.kr.card ≤ 1 ∧ C9T32.kc.card ≤ 1 := by decide +kernel

theorem C9T32_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T32.Integral p := by
  apply C9T32_integral p
  intro hd
  have hpos : 0 < C9T32_den := by decide +kernel
  have hbound : C9T32_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T32_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T32.kr, castV p (C9T32.rload d) ≠ 0) ∧
    (∀ d ∈ C9T32.kc, castV p (C9T32.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T32.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T32.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T32_large_integral
#print axioms C9T32_reduced_loads_nonzero

theorem C9T33_small_kills : C9T33.kr.card ≤ 1 ∧ C9T33.kc.card ≤ 1 := by decide +kernel

theorem C9T33_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T33.Integral p := by
  apply C9T33_integral p
  intro hd
  have hpos : 0 < C9T33_den := by decide +kernel
  have hbound : C9T33_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T33_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T33.kr, castV p (C9T33.rload d) ≠ 0) ∧
    (∀ d ∈ C9T33.kc, castV p (C9T33.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T33.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T33.kc = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T33_cload_1]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T33_large_integral
#print axioms C9T33_reduced_loads_nonzero

theorem C9T34_small_kills : C9T34.kr.card ≤ 1 ∧ C9T34.kc.card ≤ 1 := by decide +kernel

theorem C9T34_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T34.Integral p := by
  apply C9T34_integral p
  intro hd
  have hpos : 0 < C9T34_den := by decide +kernel
  have hbound : C9T34_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T34_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T34.kr, castV p (C9T34.rload d) ≠ 0) ∧
    (∀ d ∈ C9T34.kc, castV p (C9T34.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T34.kr = {1} := rfl
    have hde : d = 1 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T34_rload_1]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T34.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T34_large_integral
#print axioms C9T34_reduced_loads_nonzero

theorem C9T35_small_kills : C9T35.kr.card ≤ 1 ∧ C9T35.kc.card ≤ 1 := by decide +kernel

theorem C9T35_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T35.Integral p := by
  apply C9T35_integral p
  intro hd
  have hpos : 0 < C9T35_den := by decide +kernel
  have hbound : C9T35_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T35_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T35.kr, castV p (C9T35.rload d) ≠ 0) ∧
    (∀ d ∈ C9T35.kc, castV p (C9T35.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T35.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T35_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T35.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T35_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T35_large_integral
#print axioms C9T35_reduced_loads_nonzero

theorem C9T36_small_kills : C9T36.kr.card ≤ 1 ∧ C9T36.kc.card ≤ 1 := by decide +kernel

theorem C9T36_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T36.Integral p := by
  apply C9T36_integral p
  intro hd
  have hpos : 0 < C9T36_den := by decide +kernel
  have hbound : C9T36_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T36_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T36.kr, castV p (C9T36.rload d) ≠ 0) ∧
    (∀ d ∈ C9T36.kc, castV p (C9T36.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T36.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T36_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (-7 / 4)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T36.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T36_large_integral
#print axioms C9T36_reduced_loads_nonzero

theorem C9T37_small_kills : C9T37.kr.card ≤ 1 ∧ C9T37.kc.card ≤ 1 := by decide +kernel

theorem C9T37_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T37.Integral p := by
  apply C9T37_integral p
  intro hd
  have hpos : 0 < C9T37_den := by decide +kernel
  have hbound : C9T37_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T37_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T37.kr, castV p (C9T37.rload d) ≠ 0) ∧
    (∀ d ∈ C9T37.kc, castV p (C9T37.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T37.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T37.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T37_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (-7 / 4)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T37_large_integral
#print axioms C9T37_reduced_loads_nonzero

theorem C9T38_small_kills : C9T38.kr.card ≤ 1 ∧ C9T38.kc.card ≤ 1 := by decide +kernel

theorem C9T38_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T38.Integral p := by
  apply C9T38_integral p
  intro hd
  have hpos : 0 < C9T38_den := by decide +kernel
  have hbound : C9T38_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T38_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T38.kr, castV p (C9T38.rload d) ≠ 0) ∧
    (∀ d ∈ C9T38.kc, castV p (C9T38.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T38.kr = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T38_rload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro d hd
    have he : C9T38.kc = ∅ := rfl
    simp [he] at hd

#print axioms C9T38_large_integral
#print axioms C9T38_reduced_loads_nonzero

theorem C9T39_small_kills : C9T39.kr.card ≤ 1 ∧ C9T39.kc.card ≤ 1 := by decide +kernel

theorem C9T39_large_integral (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    C9T39.Integral p := by
  apply C9T39_integral p
  intro hd
  have hpos : 0 < C9T39_den := by decide +kernel
  have hbound : C9T39_den ≤ rankPrimeCutoff := by decide +kernel
  have hle := Nat.le_of_dvd hpos hd
  omega

theorem C9T39_reduced_loads_nonzero (p : ℕ) [Fact p.Prime] (hp : rankPrimeCutoff < p) :
    (∀ d ∈ C9T39.kr, castV p (C9T39.rload d) ≠ 0) ∧
    (∀ d ∈ C9T39.kc, castV p (C9T39.cload d) ≠ 0) := by
  constructor
  · intro d hd
    have he : C9T39.kr = ∅ := rfl
    simp [he] at hd
  · intro d hd
    have he : C9T39.kc = {0} := rfl
    have hde : d = 0 := Finset.mem_singleton.1 (by simpa only [he] using hd)
    subst d
    rw [C9T39_cload_0]
    exact rank_castV_ne_zero_of_fst p ((1 / 1), (0 / 1)) hp
      (by decide +kernel) (by decide +kernel) (by decide +kernel)

#print axioms C9T39_large_integral
#print axioms C9T39_reduced_loads_nonzero

end CatalanCore.Uniform.Bank.Sevenths.RankLoads
