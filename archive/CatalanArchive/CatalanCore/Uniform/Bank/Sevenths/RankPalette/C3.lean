import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C3
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer
theorem C3T00_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T00_den) :
    C3T00.Integral p :=
  FibreCert.integral_of_denOk C3T00 C3T00_den p C3T00_den_ok hp

theorem C3T00_palette :
    (∀ d ∈ C3T00.R, C3T00.lf d = poleL 5 0 d ∧ C3T00.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T00.C, C3T00.lf d = poleL 5 0 d ∧ C3T00.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T00_integral
#print axioms C3T00_palette

theorem C3T01_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T01_den) :
    C3T01.Integral p :=
  FibreCert.integral_of_denOk C3T01 C3T01_den p C3T01_den_ok hp

theorem C3T01_palette :
    (∀ d ∈ C3T01.R, C3T01.lf d = poleL 5 0 d ∧ C3T01.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T01.C, C3T01.lf d = poleL 5 0 d ∧ C3T01.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T01_integral
#print axioms C3T01_palette

theorem C3T02_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T02_den) :
    C3T02.Integral p :=
  FibreCert.integral_of_denOk C3T02 C3T02_den p C3T02_den_ok hp

theorem C3T02_palette :
    (∀ d ∈ C3T02.R, C3T02.lf d = poleL 5 1 d ∧ C3T02.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T02.C, C3T02.lf d = poleL 5 1 d ∧ C3T02.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T02_integral
#print axioms C3T02_palette

theorem C3T03_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T03_den) :
    C3T03.Integral p :=
  FibreCert.integral_of_denOk C3T03 C3T03_den p C3T03_den_ok hp

theorem C3T03_palette :
    (∀ d ∈ C3T03.R, C3T03.lf d = poleL 5 1 d ∧ C3T03.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T03.C, C3T03.lf d = poleL 5 1 d ∧ C3T03.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T03_integral
#print axioms C3T03_palette

theorem C3T04_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T04_den) :
    C3T04.Integral p :=
  FibreCert.integral_of_denOk C3T04 C3T04_den p C3T04_den_ok hp

theorem C3T04_palette :
    (∀ d ∈ C3T04.R, C3T04.lf d = poleL 5 1 d ∧ C3T04.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T04.C, C3T04.lf d = poleL 5 1 d ∧ C3T04.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T04_integral
#print axioms C3T04_palette

theorem C3T05_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T05_den) :
    C3T05.Integral p :=
  FibreCert.integral_of_denOk C3T05 C3T05_den p C3T05_den_ok hp

theorem C3T05_palette :
    (∀ d ∈ C3T05.R, C3T05.lf d = poleL 5 1 d ∧ C3T05.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T05.C, C3T05.lf d = poleL 5 1 d ∧ C3T05.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T05_integral
#print axioms C3T05_palette

theorem C3T06_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T06_den) :
    C3T06.Integral p :=
  FibreCert.integral_of_denOk C3T06 C3T06_den p C3T06_den_ok hp

theorem C3T06_palette :
    (∀ d ∈ C3T06.R, C3T06.lf d = poleL 5 1 d ∧ C3T06.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T06.C, C3T06.lf d = poleL 5 1 d ∧ C3T06.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T06_integral
#print axioms C3T06_palette

theorem C3T07_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T07_den) :
    C3T07.Integral p :=
  FibreCert.integral_of_denOk C3T07 C3T07_den p C3T07_den_ok hp

theorem C3T07_palette :
    (∀ d ∈ C3T07.R, C3T07.lf d = poleL 5 0 d ∧ C3T07.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T07.C, C3T07.lf d = poleL 5 0 d ∧ C3T07.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T07_integral
#print axioms C3T07_palette

theorem C3T08_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T08_den) :
    C3T08.Integral p :=
  FibreCert.integral_of_denOk C3T08 C3T08_den p C3T08_den_ok hp

theorem C3T08_palette :
    (∀ d ∈ C3T08.R, C3T08.lf d = poleL 5 0 d ∧ C3T08.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T08.C, C3T08.lf d = poleL 5 0 d ∧ C3T08.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T08_integral
#print axioms C3T08_palette

theorem C3T09_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T09_den) :
    C3T09.Integral p :=
  FibreCert.integral_of_denOk C3T09 C3T09_den p C3T09_den_ok hp

theorem C3T09_palette :
    (∀ d ∈ C3T09.R, C3T09.lf d = poleL 5 0 d ∧ C3T09.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T09.C, C3T09.lf d = poleL 5 0 d ∧ C3T09.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T09_integral
#print axioms C3T09_palette

theorem C3T10_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T10_den) :
    C3T10.Integral p :=
  FibreCert.integral_of_denOk C3T10 C3T10_den p C3T10_den_ok hp

theorem C3T10_palette :
    (∀ d ∈ C3T10.R, C3T10.lf d = poleL 5 1 d ∧ C3T10.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T10.C, C3T10.lf d = poleL 5 1 d ∧ C3T10.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T10_integral
#print axioms C3T10_palette

theorem C3T11_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T11_den) :
    C3T11.Integral p :=
  FibreCert.integral_of_denOk C3T11 C3T11_den p C3T11_den_ok hp

theorem C3T11_palette :
    (∀ d ∈ C3T11.R, C3T11.lf d = poleL 5 1 d ∧ C3T11.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T11.C, C3T11.lf d = poleL 5 1 d ∧ C3T11.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T11_integral
#print axioms C3T11_palette

theorem C3T12_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T12_den) :
    C3T12.Integral p :=
  FibreCert.integral_of_denOk C3T12 C3T12_den p C3T12_den_ok hp

theorem C3T12_palette :
    (∀ d ∈ C3T12.R, C3T12.lf d = poleL 5 1 d ∧ C3T12.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T12.C, C3T12.lf d = poleL 5 1 d ∧ C3T12.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T12_integral
#print axioms C3T12_palette

theorem C3T13_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T13_den) :
    C3T13.Integral p :=
  FibreCert.integral_of_denOk C3T13 C3T13_den p C3T13_den_ok hp

theorem C3T13_palette :
    (∀ d ∈ C3T13.R, C3T13.lf d = poleL 5 0 d ∧ C3T13.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T13.C, C3T13.lf d = poleL 5 0 d ∧ C3T13.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T13_integral
#print axioms C3T13_palette

theorem C3T14_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T14_den) :
    C3T14.Integral p :=
  FibreCert.integral_of_denOk C3T14 C3T14_den p C3T14_den_ok hp

theorem C3T14_palette :
    (∀ d ∈ C3T14.R, C3T14.lf d = poleL 5 0 d ∧ C3T14.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T14.C, C3T14.lf d = poleL 5 0 d ∧ C3T14.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T14_integral
#print axioms C3T14_palette

theorem C3T15_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T15_den) :
    C3T15.Integral p :=
  FibreCert.integral_of_denOk C3T15 C3T15_den p C3T15_den_ok hp

theorem C3T15_palette :
    (∀ d ∈ C3T15.R, C3T15.lf d = poleL 5 0 d ∧ C3T15.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T15.C, C3T15.lf d = poleL 5 0 d ∧ C3T15.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T15_integral
#print axioms C3T15_palette

theorem C3T16_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T16_den) :
    C3T16.Integral p :=
  FibreCert.integral_of_denOk C3T16 C3T16_den p C3T16_den_ok hp

theorem C3T16_palette :
    (∀ d ∈ C3T16.R, C3T16.lf d = poleL 5 1 d ∧ C3T16.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T16.C, C3T16.lf d = poleL 5 1 d ∧ C3T16.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T16_integral
#print axioms C3T16_palette

theorem C3T17_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T17_den) :
    C3T17.Integral p :=
  FibreCert.integral_of_denOk C3T17 C3T17_den p C3T17_den_ok hp

theorem C3T17_palette :
    (∀ d ∈ C3T17.R, C3T17.lf d = poleL 5 0 d ∧ C3T17.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T17.C, C3T17.lf d = poleL 5 0 d ∧ C3T17.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T17_integral
#print axioms C3T17_palette

theorem C3T18_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T18_den) :
    C3T18.Integral p :=
  FibreCert.integral_of_denOk C3T18 C3T18_den p C3T18_den_ok hp

theorem C3T18_palette :
    (∀ d ∈ C3T18.R, C3T18.lf d = poleL 5 1 d ∧ C3T18.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T18.C, C3T18.lf d = poleL 5 1 d ∧ C3T18.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T18_integral
#print axioms C3T18_palette

theorem C3T19_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T19_den) :
    C3T19.Integral p :=
  FibreCert.integral_of_denOk C3T19 C3T19_den p C3T19_den_ok hp

theorem C3T19_palette :
    (∀ d ∈ C3T19.R, C3T19.lf d = poleL 5 1 d ∧ C3T19.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T19.C, C3T19.lf d = poleL 5 1 d ∧ C3T19.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T19_integral
#print axioms C3T19_palette

theorem C3T20_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T20_den) :
    C3T20.Integral p :=
  FibreCert.integral_of_denOk C3T20 C3T20_den p C3T20_den_ok hp

theorem C3T20_palette :
    (∀ d ∈ C3T20.R, C3T20.lf d = poleL 5 0 d ∧ C3T20.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T20.C, C3T20.lf d = poleL 5 0 d ∧ C3T20.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T20_integral
#print axioms C3T20_palette

theorem C3T21_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T21_den) :
    C3T21.Integral p :=
  FibreCert.integral_of_denOk C3T21 C3T21_den p C3T21_den_ok hp

theorem C3T21_palette :
    (∀ d ∈ C3T21.R, C3T21.lf d = poleL 5 0 d ∧ C3T21.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T21.C, C3T21.lf d = poleL 5 0 d ∧ C3T21.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T21_integral
#print axioms C3T21_palette

theorem C3T22_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T22_den) :
    C3T22.Integral p :=
  FibreCert.integral_of_denOk C3T22 C3T22_den p C3T22_den_ok hp

theorem C3T22_palette :
    (∀ d ∈ C3T22.R, C3T22.lf d = poleL 5 1 d ∧ C3T22.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T22.C, C3T22.lf d = poleL 5 1 d ∧ C3T22.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T22_integral
#print axioms C3T22_palette

theorem C3T23_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T23_den) :
    C3T23.Integral p :=
  FibreCert.integral_of_denOk C3T23 C3T23_den p C3T23_den_ok hp

theorem C3T23_palette :
    (∀ d ∈ C3T23.R, C3T23.lf d = poleL 5 0 d ∧ C3T23.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T23.C, C3T23.lf d = poleL 5 0 d ∧ C3T23.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T23_integral
#print axioms C3T23_palette

theorem C3T24_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T24_den) :
    C3T24.Integral p :=
  FibreCert.integral_of_denOk C3T24 C3T24_den p C3T24_den_ok hp

theorem C3T24_palette :
    (∀ d ∈ C3T24.R, C3T24.lf d = poleL 5 1 d ∧ C3T24.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T24.C, C3T24.lf d = poleL 5 1 d ∧ C3T24.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T24_integral
#print axioms C3T24_palette

theorem C3T25_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T25_den) :
    C3T25.Integral p :=
  FibreCert.integral_of_denOk C3T25 C3T25_den p C3T25_den_ok hp

theorem C3T25_palette :
    (∀ d ∈ C3T25.R, C3T25.lf d = poleL 5 1 d ∧ C3T25.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T25.C, C3T25.lf d = poleL 5 1 d ∧ C3T25.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T25_integral
#print axioms C3T25_palette

theorem C3T26_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T26_den) :
    C3T26.Integral p :=
  FibreCert.integral_of_denOk C3T26 C3T26_den p C3T26_den_ok hp

theorem C3T26_palette :
    (∀ d ∈ C3T26.R, C3T26.lf d = poleL 5 0 d ∧ C3T26.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T26.C, C3T26.lf d = poleL 5 0 d ∧ C3T26.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T26_integral
#print axioms C3T26_palette

theorem C3T27_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T27_den) :
    C3T27.Integral p :=
  FibreCert.integral_of_denOk C3T27 C3T27_den p C3T27_den_ok hp

theorem C3T27_palette :
    (∀ d ∈ C3T27.R, C3T27.lf d = poleL 5 0 d ∧ C3T27.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T27.C, C3T27.lf d = poleL 5 0 d ∧ C3T27.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T27_integral
#print axioms C3T27_palette

theorem C3T28_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T28_den) :
    C3T28.Integral p :=
  FibreCert.integral_of_denOk C3T28 C3T28_den p C3T28_den_ok hp

theorem C3T28_palette :
    (∀ d ∈ C3T28.R, C3T28.lf d = poleL 5 1 d ∧ C3T28.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T28.C, C3T28.lf d = poleL 5 1 d ∧ C3T28.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T28_integral
#print axioms C3T28_palette

theorem C3T29_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T29_den) :
    C3T29.Integral p :=
  FibreCert.integral_of_denOk C3T29 C3T29_den p C3T29_den_ok hp

theorem C3T29_palette :
    (∀ d ∈ C3T29.R, C3T29.lf d = poleL 5 0 d ∧ C3T29.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T29.C, C3T29.lf d = poleL 5 0 d ∧ C3T29.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T29_integral
#print axioms C3T29_palette

theorem C3T30_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T30_den) :
    C3T30.Integral p :=
  FibreCert.integral_of_denOk C3T30 C3T30_den p C3T30_den_ok hp

theorem C3T30_palette :
    (∀ d ∈ C3T30.R, C3T30.lf d = poleL 5 1 d ∧ C3T30.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T30.C, C3T30.lf d = poleL 5 1 d ∧ C3T30.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T30_integral
#print axioms C3T30_palette

theorem C3T31_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T31_den) :
    C3T31.Integral p :=
  FibreCert.integral_of_denOk C3T31 C3T31_den p C3T31_den_ok hp

theorem C3T31_palette :
    (∀ d ∈ C3T31.R, C3T31.lf d = poleL 5 1 d ∧ C3T31.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T31.C, C3T31.lf d = poleL 5 1 d ∧ C3T31.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T31_integral
#print axioms C3T31_palette

theorem C3T32_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T32_den) :
    C3T32.Integral p :=
  FibreCert.integral_of_denOk C3T32 C3T32_den p C3T32_den_ok hp

theorem C3T32_palette :
    (∀ d ∈ C3T32.R, C3T32.lf d = poleL 5 0 d ∧ C3T32.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T32.C, C3T32.lf d = poleL 5 0 d ∧ C3T32.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T32_integral
#print axioms C3T32_palette

theorem C3T33_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T33_den) :
    C3T33.Integral p :=
  FibreCert.integral_of_denOk C3T33 C3T33_den p C3T33_den_ok hp

theorem C3T33_palette :
    (∀ d ∈ C3T33.R, C3T33.lf d = poleL 5 0 d ∧ C3T33.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T33.C, C3T33.lf d = poleL 5 0 d ∧ C3T33.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T33_integral
#print axioms C3T33_palette

theorem C3T34_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T34_den) :
    C3T34.Integral p :=
  FibreCert.integral_of_denOk C3T34 C3T34_den p C3T34_den_ok hp

theorem C3T34_palette :
    (∀ d ∈ C3T34.R, C3T34.lf d = poleL 5 1 d ∧ C3T34.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T34.C, C3T34.lf d = poleL 5 1 d ∧ C3T34.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T34_integral
#print axioms C3T34_palette

theorem C3T35_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T35_den) :
    C3T35.Integral p :=
  FibreCert.integral_of_denOk C3T35 C3T35_den p C3T35_den_ok hp

theorem C3T35_palette :
    (∀ d ∈ C3T35.R, C3T35.lf d = poleL 5 0 d ∧ C3T35.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T35.C, C3T35.lf d = poleL 5 0 d ∧ C3T35.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T35_integral
#print axioms C3T35_palette

theorem C3T36_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T36_den) :
    C3T36.Integral p :=
  FibreCert.integral_of_denOk C3T36 C3T36_den p C3T36_den_ok hp

theorem C3T36_palette :
    (∀ d ∈ C3T36.R, C3T36.lf d = poleL 5 1 d ∧ C3T36.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T36.C, C3T36.lf d = poleL 5 1 d ∧ C3T36.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T36_integral
#print axioms C3T36_palette

theorem C3T37_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T37_den) :
    C3T37.Integral p :=
  FibreCert.integral_of_denOk C3T37 C3T37_den p C3T37_den_ok hp

theorem C3T37_palette :
    (∀ d ∈ C3T37.R, C3T37.lf d = poleL 5 1 d ∧ C3T37.ee d = poleE 5 1 d) ∧
    (∀ d ∈ C3T37.C, C3T37.lf d = poleL 5 1 d ∧ C3T37.ee d = poleE 5 1 d) := by
  constructor <;> decide +kernel

#print axioms C3T37_integral
#print axioms C3T37_palette

theorem C3T38_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T38_den) :
    C3T38.Integral p :=
  FibreCert.integral_of_denOk C3T38 C3T38_den p C3T38_den_ok hp

theorem C3T38_palette :
    (∀ d ∈ C3T38.R, C3T38.lf d = poleL 5 0 d ∧ C3T38.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T38.C, C3T38.lf d = poleL 5 0 d ∧ C3T38.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T38_integral
#print axioms C3T38_palette

theorem C3T39_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T39_den) :
    C3T39.Integral p :=
  FibreCert.integral_of_denOk C3T39 C3T39_den p C3T39_den_ok hp

theorem C3T39_palette :
    (∀ d ∈ C3T39.R, C3T39.lf d = poleL 5 0 d ∧ C3T39.ee d = poleE 5 0 d) ∧
    (∀ d ∈ C3T39.C, C3T39.lf d = poleL 5 0 d ∧ C3T39.ee d = poleE 5 0 d) := by
  constructor <;> decide +kernel

#print axioms C3T39_integral
#print axioms C3T39_palette

end CatalanCore.Uniform.Bank.Sevenths.RankData
