import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C5
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer
theorem C5T00_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T00_den) :
    C5T00.Integral p :=
  FibreCert.integral_of_denOk C5T00 C5T00_den p C5T00_den_ok hp

theorem C5T00_palette :
    (∀ d ∈ C5T00.R, C5T00.lf d = poleL 3 0 d ∧ C5T00.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T00.C, C5T00.lf d = poleL 3 0 d ∧ C5T00.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T00_integral
#print axioms C5T00_palette

theorem C5T01_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T01_den) :
    C5T01.Integral p :=
  FibreCert.integral_of_denOk C5T01 C5T01_den p C5T01_den_ok hp

theorem C5T01_palette :
    (∀ d ∈ C5T01.R, C5T01.lf d = poleL 3 0 d ∧ C5T01.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T01.C, C5T01.lf d = poleL 3 0 d ∧ C5T01.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T01_integral
#print axioms C5T01_palette

theorem C5T02_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T02_den) :
    C5T02.Integral p :=
  FibreCert.integral_of_denOk C5T02 C5T02_den p C5T02_den_ok hp

theorem C5T02_palette :
    (∀ d ∈ C5T02.R, C5T02.lf d = poleL 3 1 d ∧ C5T02.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T02.C, C5T02.lf d = poleL 3 1 d ∧ C5T02.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T02_integral
#print axioms C5T02_palette

theorem C5T03_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T03_den) :
    C5T03.Integral p :=
  FibreCert.integral_of_denOk C5T03 C5T03_den p C5T03_den_ok hp

theorem C5T03_palette :
    (∀ d ∈ C5T03.R, C5T03.lf d = poleL 3 1 d ∧ C5T03.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T03.C, C5T03.lf d = poleL 3 1 d ∧ C5T03.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T03_integral
#print axioms C5T03_palette

theorem C5T04_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T04_den) :
    C5T04.Integral p :=
  FibreCert.integral_of_denOk C5T04 C5T04_den p C5T04_den_ok hp

theorem C5T04_palette :
    (∀ d ∈ C5T04.R, C5T04.lf d = poleL 3 1 d ∧ C5T04.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T04.C, C5T04.lf d = poleL 3 1 d ∧ C5T04.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T04_integral
#print axioms C5T04_palette

theorem C5T05_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T05_den) :
    C5T05.Integral p :=
  FibreCert.integral_of_denOk C5T05 C5T05_den p C5T05_den_ok hp

theorem C5T05_palette :
    (∀ d ∈ C5T05.R, C5T05.lf d = poleL 3 1 d ∧ C5T05.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T05.C, C5T05.lf d = poleL 3 1 d ∧ C5T05.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T05_integral
#print axioms C5T05_palette

theorem C5T06_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T06_den) :
    C5T06.Integral p :=
  FibreCert.integral_of_denOk C5T06 C5T06_den p C5T06_den_ok hp

theorem C5T06_palette :
    (∀ d ∈ C5T06.R, C5T06.lf d = poleL 3 1 d ∧ C5T06.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T06.C, C5T06.lf d = poleL 3 1 d ∧ C5T06.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T06_integral
#print axioms C5T06_palette

theorem C5T07_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T07_den) :
    C5T07.Integral p :=
  FibreCert.integral_of_denOk C5T07 C5T07_den p C5T07_den_ok hp

theorem C5T07_palette :
    (∀ d ∈ C5T07.R, C5T07.lf d = poleL 3 0 d ∧ C5T07.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T07.C, C5T07.lf d = poleL 3 0 d ∧ C5T07.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T07_integral
#print axioms C5T07_palette

theorem C5T08_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T08_den) :
    C5T08.Integral p :=
  FibreCert.integral_of_denOk C5T08 C5T08_den p C5T08_den_ok hp

theorem C5T08_palette :
    (∀ d ∈ C5T08.R, C5T08.lf d = poleL 3 0 d ∧ C5T08.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T08.C, C5T08.lf d = poleL 3 0 d ∧ C5T08.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T08_integral
#print axioms C5T08_palette

theorem C5T09_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T09_den) :
    C5T09.Integral p :=
  FibreCert.integral_of_denOk C5T09 C5T09_den p C5T09_den_ok hp

theorem C5T09_palette :
    (∀ d ∈ C5T09.R, C5T09.lf d = poleL 3 0 d ∧ C5T09.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T09.C, C5T09.lf d = poleL 3 0 d ∧ C5T09.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T09_integral
#print axioms C5T09_palette

theorem C5T10_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T10_den) :
    C5T10.Integral p :=
  FibreCert.integral_of_denOk C5T10 C5T10_den p C5T10_den_ok hp

theorem C5T10_palette :
    (∀ d ∈ C5T10.R, C5T10.lf d = poleL 3 1 d ∧ C5T10.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T10.C, C5T10.lf d = poleL 3 1 d ∧ C5T10.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T10_integral
#print axioms C5T10_palette

theorem C5T11_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T11_den) :
    C5T11.Integral p :=
  FibreCert.integral_of_denOk C5T11 C5T11_den p C5T11_den_ok hp

theorem C5T11_palette :
    (∀ d ∈ C5T11.R, C5T11.lf d = poleL 3 1 d ∧ C5T11.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T11.C, C5T11.lf d = poleL 3 1 d ∧ C5T11.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T11_integral
#print axioms C5T11_palette

theorem C5T12_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T12_den) :
    C5T12.Integral p :=
  FibreCert.integral_of_denOk C5T12 C5T12_den p C5T12_den_ok hp

theorem C5T12_palette :
    (∀ d ∈ C5T12.R, C5T12.lf d = poleL 3 1 d ∧ C5T12.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T12.C, C5T12.lf d = poleL 3 1 d ∧ C5T12.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T12_integral
#print axioms C5T12_palette

theorem C5T13_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T13_den) :
    C5T13.Integral p :=
  FibreCert.integral_of_denOk C5T13 C5T13_den p C5T13_den_ok hp

theorem C5T13_palette :
    (∀ d ∈ C5T13.R, C5T13.lf d = poleL 3 0 d ∧ C5T13.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T13.C, C5T13.lf d = poleL 3 0 d ∧ C5T13.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T13_integral
#print axioms C5T13_palette

theorem C5T14_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T14_den) :
    C5T14.Integral p :=
  FibreCert.integral_of_denOk C5T14 C5T14_den p C5T14_den_ok hp

theorem C5T14_palette :
    (∀ d ∈ C5T14.R, C5T14.lf d = poleL 3 0 d ∧ C5T14.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T14.C, C5T14.lf d = poleL 3 0 d ∧ C5T14.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T14_integral
#print axioms C5T14_palette

theorem C5T15_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T15_den) :
    C5T15.Integral p :=
  FibreCert.integral_of_denOk C5T15 C5T15_den p C5T15_den_ok hp

theorem C5T15_palette :
    (∀ d ∈ C5T15.R, C5T15.lf d = poleL 3 0 d ∧ C5T15.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T15.C, C5T15.lf d = poleL 3 0 d ∧ C5T15.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T15_integral
#print axioms C5T15_palette

theorem C5T16_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T16_den) :
    C5T16.Integral p :=
  FibreCert.integral_of_denOk C5T16 C5T16_den p C5T16_den_ok hp

theorem C5T16_palette :
    (∀ d ∈ C5T16.R, C5T16.lf d = poleL 3 1 d ∧ C5T16.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T16.C, C5T16.lf d = poleL 3 1 d ∧ C5T16.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T16_integral
#print axioms C5T16_palette

theorem C5T17_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T17_den) :
    C5T17.Integral p :=
  FibreCert.integral_of_denOk C5T17 C5T17_den p C5T17_den_ok hp

theorem C5T17_palette :
    (∀ d ∈ C5T17.R, C5T17.lf d = poleL 3 1 d ∧ C5T17.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T17.C, C5T17.lf d = poleL 3 1 d ∧ C5T17.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T17_integral
#print axioms C5T17_palette

theorem C5T18_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T18_den) :
    C5T18.Integral p :=
  FibreCert.integral_of_denOk C5T18 C5T18_den p C5T18_den_ok hp

theorem C5T18_palette :
    (∀ d ∈ C5T18.R, C5T18.lf d = poleL 3 1 d ∧ C5T18.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T18.C, C5T18.lf d = poleL 3 1 d ∧ C5T18.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T18_integral
#print axioms C5T18_palette

theorem C5T19_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T19_den) :
    C5T19.Integral p :=
  FibreCert.integral_of_denOk C5T19 C5T19_den p C5T19_den_ok hp

theorem C5T19_palette :
    (∀ d ∈ C5T19.R, C5T19.lf d = poleL 3 0 d ∧ C5T19.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T19.C, C5T19.lf d = poleL 3 0 d ∧ C5T19.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T19_integral
#print axioms C5T19_palette

theorem C5T20_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T20_den) :
    C5T20.Integral p :=
  FibreCert.integral_of_denOk C5T20 C5T20_den p C5T20_den_ok hp

theorem C5T20_palette :
    (∀ d ∈ C5T20.R, C5T20.lf d = poleL 3 0 d ∧ C5T20.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T20.C, C5T20.lf d = poleL 3 0 d ∧ C5T20.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T20_integral
#print axioms C5T20_palette

theorem C5T21_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T21_den) :
    C5T21.Integral p :=
  FibreCert.integral_of_denOk C5T21 C5T21_den p C5T21_den_ok hp

theorem C5T21_palette :
    (∀ d ∈ C5T21.R, C5T21.lf d = poleL 3 0 d ∧ C5T21.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T21.C, C5T21.lf d = poleL 3 0 d ∧ C5T21.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T21_integral
#print axioms C5T21_palette

theorem C5T22_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T22_den) :
    C5T22.Integral p :=
  FibreCert.integral_of_denOk C5T22 C5T22_den p C5T22_den_ok hp

theorem C5T22_palette :
    (∀ d ∈ C5T22.R, C5T22.lf d = poleL 3 1 d ∧ C5T22.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T22.C, C5T22.lf d = poleL 3 1 d ∧ C5T22.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T22_integral
#print axioms C5T22_palette

theorem C5T23_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T23_den) :
    C5T23.Integral p :=
  FibreCert.integral_of_denOk C5T23 C5T23_den p C5T23_den_ok hp

theorem C5T23_palette :
    (∀ d ∈ C5T23.R, C5T23.lf d = poleL 3 1 d ∧ C5T23.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T23.C, C5T23.lf d = poleL 3 1 d ∧ C5T23.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T23_integral
#print axioms C5T23_palette

theorem C5T24_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T24_den) :
    C5T24.Integral p :=
  FibreCert.integral_of_denOk C5T24 C5T24_den p C5T24_den_ok hp

theorem C5T24_palette :
    (∀ d ∈ C5T24.R, C5T24.lf d = poleL 3 1 d ∧ C5T24.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T24.C, C5T24.lf d = poleL 3 1 d ∧ C5T24.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T24_integral
#print axioms C5T24_palette

theorem C5T25_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T25_den) :
    C5T25.Integral p :=
  FibreCert.integral_of_denOk C5T25 C5T25_den p C5T25_den_ok hp

theorem C5T25_palette :
    (∀ d ∈ C5T25.R, C5T25.lf d = poleL 3 0 d ∧ C5T25.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T25.C, C5T25.lf d = poleL 3 0 d ∧ C5T25.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T25_integral
#print axioms C5T25_palette

theorem C5T26_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T26_den) :
    C5T26.Integral p :=
  FibreCert.integral_of_denOk C5T26 C5T26_den p C5T26_den_ok hp

theorem C5T26_palette :
    (∀ d ∈ C5T26.R, C5T26.lf d = poleL 3 1 d ∧ C5T26.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T26.C, C5T26.lf d = poleL 3 1 d ∧ C5T26.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T26_integral
#print axioms C5T26_palette

theorem C5T27_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T27_den) :
    C5T27.Integral p :=
  FibreCert.integral_of_denOk C5T27 C5T27_den p C5T27_den_ok hp

theorem C5T27_palette :
    (∀ d ∈ C5T27.R, C5T27.lf d = poleL 3 0 d ∧ C5T27.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T27.C, C5T27.lf d = poleL 3 0 d ∧ C5T27.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T27_integral
#print axioms C5T27_palette

theorem C5T28_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T28_den) :
    C5T28.Integral p :=
  FibreCert.integral_of_denOk C5T28 C5T28_den p C5T28_den_ok hp

theorem C5T28_palette :
    (∀ d ∈ C5T28.R, C5T28.lf d = poleL 3 0 d ∧ C5T28.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T28.C, C5T28.lf d = poleL 3 0 d ∧ C5T28.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T28_integral
#print axioms C5T28_palette

theorem C5T29_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T29_den) :
    C5T29.Integral p :=
  FibreCert.integral_of_denOk C5T29 C5T29_den p C5T29_den_ok hp

theorem C5T29_palette :
    (∀ d ∈ C5T29.R, C5T29.lf d = poleL 3 0 d ∧ C5T29.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T29.C, C5T29.lf d = poleL 3 0 d ∧ C5T29.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T29_integral
#print axioms C5T29_palette

theorem C5T30_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T30_den) :
    C5T30.Integral p :=
  FibreCert.integral_of_denOk C5T30 C5T30_den p C5T30_den_ok hp

theorem C5T30_palette :
    (∀ d ∈ C5T30.R, C5T30.lf d = poleL 3 1 d ∧ C5T30.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T30.C, C5T30.lf d = poleL 3 1 d ∧ C5T30.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T30_integral
#print axioms C5T30_palette

theorem C5T31_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T31_den) :
    C5T31.Integral p :=
  FibreCert.integral_of_denOk C5T31 C5T31_den p C5T31_den_ok hp

theorem C5T31_palette :
    (∀ d ∈ C5T31.R, C5T31.lf d = poleL 3 1 d ∧ C5T31.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T31.C, C5T31.lf d = poleL 3 1 d ∧ C5T31.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T31_integral
#print axioms C5T31_palette

theorem C5T32_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T32_den) :
    C5T32.Integral p :=
  FibreCert.integral_of_denOk C5T32 C5T32_den p C5T32_den_ok hp

theorem C5T32_palette :
    (∀ d ∈ C5T32.R, C5T32.lf d = poleL 3 1 d ∧ C5T32.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T32.C, C5T32.lf d = poleL 3 1 d ∧ C5T32.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T32_integral
#print axioms C5T32_palette

theorem C5T33_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T33_den) :
    C5T33.Integral p :=
  FibreCert.integral_of_denOk C5T33 C5T33_den p C5T33_den_ok hp

theorem C5T33_palette :
    (∀ d ∈ C5T33.R, C5T33.lf d = poleL 3 0 d ∧ C5T33.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T33.C, C5T33.lf d = poleL 3 0 d ∧ C5T33.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T33_integral
#print axioms C5T33_palette

theorem C5T34_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T34_den) :
    C5T34.Integral p :=
  FibreCert.integral_of_denOk C5T34 C5T34_den p C5T34_den_ok hp

theorem C5T34_palette :
    (∀ d ∈ C5T34.R, C5T34.lf d = poleL 3 0 d ∧ C5T34.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T34.C, C5T34.lf d = poleL 3 0 d ∧ C5T34.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T34_integral
#print axioms C5T34_palette

theorem C5T35_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T35_den) :
    C5T35.Integral p :=
  FibreCert.integral_of_denOk C5T35 C5T35_den p C5T35_den_ok hp

theorem C5T35_palette :
    (∀ d ∈ C5T35.R, C5T35.lf d = poleL 3 0 d ∧ C5T35.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T35.C, C5T35.lf d = poleL 3 0 d ∧ C5T35.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T35_integral
#print axioms C5T35_palette

theorem C5T36_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T36_den) :
    C5T36.Integral p :=
  FibreCert.integral_of_denOk C5T36 C5T36_den p C5T36_den_ok hp

theorem C5T36_palette :
    (∀ d ∈ C5T36.R, C5T36.lf d = poleL 3 1 d ∧ C5T36.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T36.C, C5T36.lf d = poleL 3 1 d ∧ C5T36.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T36_integral
#print axioms C5T36_palette

theorem C5T37_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T37_den) :
    C5T37.Integral p :=
  FibreCert.integral_of_denOk C5T37 C5T37_den p C5T37_den_ok hp

theorem C5T37_palette :
    (∀ d ∈ C5T37.R, C5T37.lf d = poleL 3 1 d ∧ C5T37.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C5T37.C, C5T37.lf d = poleL 3 1 d ∧ C5T37.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel

#print axioms C5T37_integral
#print axioms C5T37_palette

theorem C5T38_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T38_den) :
    C5T38.Integral p :=
  FibreCert.integral_of_denOk C5T38 C5T38_den p C5T38_den_ok hp

theorem C5T38_palette :
    (∀ d ∈ C5T38.R, C5T38.lf d = poleL 3 0 d ∧ C5T38.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T38.C, C5T38.lf d = poleL 3 0 d ∧ C5T38.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T38_integral
#print axioms C5T38_palette

theorem C5T39_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C5T39_den) :
    C5T39.Integral p :=
  FibreCert.integral_of_denOk C5T39 C5T39_den p C5T39_den_ok hp

theorem C5T39_palette :
    (∀ d ∈ C5T39.R, C5T39.lf d = poleL 3 0 d ∧ C5T39.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C5T39.C, C5T39.lf d = poleL 3 0 d ∧ C5T39.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel

#print axioms C5T39_integral
#print axioms C5T39_palette

end CatalanCore.Uniform.Bank.Sevenths.RankData
