import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C1
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer
theorem C1T00_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T00_den) :
    C1T00.Integral p :=
  FibreCert.integral_of_denOk C1T00 C1T00_den p C1T00_den_ok hp

theorem C1T00_palette :
    (∀ d ∈ C1T00.R, C1T00.lf d = poleL 1 0 d ∧ C1T00.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T00.C, C1T00.lf d = poleL 1 0 d ∧ C1T00.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T00_integral
#print axioms C1T00_palette

theorem C1T01_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T01_den) :
    C1T01.Integral p :=
  FibreCert.integral_of_denOk C1T01 C1T01_den p C1T01_den_ok hp

theorem C1T01_palette :
    (∀ d ∈ C1T01.R, C1T01.lf d = poleL 1 0 d ∧ C1T01.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T01.C, C1T01.lf d = poleL 1 0 d ∧ C1T01.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T01_integral
#print axioms C1T01_palette

theorem C1T02_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T02_den) :
    C1T02.Integral p :=
  FibreCert.integral_of_denOk C1T02 C1T02_den p C1T02_den_ok hp

theorem C1T02_palette :
    (∀ d ∈ C1T02.R, C1T02.lf d = poleL 1 1 d ∧ C1T02.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T02.C, C1T02.lf d = poleL 1 1 d ∧ C1T02.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T02_integral
#print axioms C1T02_palette

theorem C1T03_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T03_den) :
    C1T03.Integral p :=
  FibreCert.integral_of_denOk C1T03 C1T03_den p C1T03_den_ok hp

theorem C1T03_palette :
    (∀ d ∈ C1T03.R, C1T03.lf d = poleL 1 1 d ∧ C1T03.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T03.C, C1T03.lf d = poleL 1 1 d ∧ C1T03.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T03_integral
#print axioms C1T03_palette

theorem C1T04_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T04_den) :
    C1T04.Integral p :=
  FibreCert.integral_of_denOk C1T04 C1T04_den p C1T04_den_ok hp

theorem C1T04_palette :
    (∀ d ∈ C1T04.R, C1T04.lf d = poleL 1 1 d ∧ C1T04.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T04.C, C1T04.lf d = poleL 1 1 d ∧ C1T04.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T04_integral
#print axioms C1T04_palette

theorem C1T05_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T05_den) :
    C1T05.Integral p :=
  FibreCert.integral_of_denOk C1T05 C1T05_den p C1T05_den_ok hp

theorem C1T05_palette :
    (∀ d ∈ C1T05.R, C1T05.lf d = poleL 1 1 d ∧ C1T05.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T05.C, C1T05.lf d = poleL 1 1 d ∧ C1T05.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T05_integral
#print axioms C1T05_palette

theorem C1T06_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T06_den) :
    C1T06.Integral p :=
  FibreCert.integral_of_denOk C1T06 C1T06_den p C1T06_den_ok hp

theorem C1T06_palette :
    (∀ d ∈ C1T06.R, C1T06.lf d = poleL 1 1 d ∧ C1T06.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T06.C, C1T06.lf d = poleL 1 1 d ∧ C1T06.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T06_integral
#print axioms C1T06_palette

theorem C1T07_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T07_den) :
    C1T07.Integral p :=
  FibreCert.integral_of_denOk C1T07 C1T07_den p C1T07_den_ok hp

theorem C1T07_palette :
    (∀ d ∈ C1T07.R, C1T07.lf d = poleL 1 0 d ∧ C1T07.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T07.C, C1T07.lf d = poleL 1 0 d ∧ C1T07.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T07_integral
#print axioms C1T07_palette

theorem C1T08_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T08_den) :
    C1T08.Integral p :=
  FibreCert.integral_of_denOk C1T08 C1T08_den p C1T08_den_ok hp

theorem C1T08_palette :
    (∀ d ∈ C1T08.R, C1T08.lf d = poleL 1 0 d ∧ C1T08.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T08.C, C1T08.lf d = poleL 1 0 d ∧ C1T08.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T08_integral
#print axioms C1T08_palette

theorem C1T09_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T09_den) :
    C1T09.Integral p :=
  FibreCert.integral_of_denOk C1T09 C1T09_den p C1T09_den_ok hp

theorem C1T09_palette :
    (∀ d ∈ C1T09.R, C1T09.lf d = poleL 1 0 d ∧ C1T09.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T09.C, C1T09.lf d = poleL 1 0 d ∧ C1T09.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T09_integral
#print axioms C1T09_palette

theorem C1T10_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T10_den) :
    C1T10.Integral p :=
  FibreCert.integral_of_denOk C1T10 C1T10_den p C1T10_den_ok hp

theorem C1T10_palette :
    (∀ d ∈ C1T10.R, C1T10.lf d = poleL 1 1 d ∧ C1T10.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T10.C, C1T10.lf d = poleL 1 1 d ∧ C1T10.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T10_integral
#print axioms C1T10_palette

theorem C1T11_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T11_den) :
    C1T11.Integral p :=
  FibreCert.integral_of_denOk C1T11 C1T11_den p C1T11_den_ok hp

theorem C1T11_palette :
    (∀ d ∈ C1T11.R, C1T11.lf d = poleL 1 1 d ∧ C1T11.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T11.C, C1T11.lf d = poleL 1 1 d ∧ C1T11.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T11_integral
#print axioms C1T11_palette

theorem C1T12_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T12_den) :
    C1T12.Integral p :=
  FibreCert.integral_of_denOk C1T12 C1T12_den p C1T12_den_ok hp

theorem C1T12_palette :
    (∀ d ∈ C1T12.R, C1T12.lf d = poleL 1 1 d ∧ C1T12.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T12.C, C1T12.lf d = poleL 1 1 d ∧ C1T12.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T12_integral
#print axioms C1T12_palette

theorem C1T13_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T13_den) :
    C1T13.Integral p :=
  FibreCert.integral_of_denOk C1T13 C1T13_den p C1T13_den_ok hp

theorem C1T13_palette :
    (∀ d ∈ C1T13.R, C1T13.lf d = poleL 1 0 d ∧ C1T13.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T13.C, C1T13.lf d = poleL 1 0 d ∧ C1T13.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T13_integral
#print axioms C1T13_palette

theorem C1T14_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T14_den) :
    C1T14.Integral p :=
  FibreCert.integral_of_denOk C1T14 C1T14_den p C1T14_den_ok hp

theorem C1T14_palette :
    (∀ d ∈ C1T14.R, C1T14.lf d = poleL 1 1 d ∧ C1T14.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T14.C, C1T14.lf d = poleL 1 1 d ∧ C1T14.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T14_integral
#print axioms C1T14_palette

theorem C1T15_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T15_den) :
    C1T15.Integral p :=
  FibreCert.integral_of_denOk C1T15 C1T15_den p C1T15_den_ok hp

theorem C1T15_palette :
    (∀ d ∈ C1T15.R, C1T15.lf d = poleL 1 0 d ∧ C1T15.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T15.C, C1T15.lf d = poleL 1 0 d ∧ C1T15.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T15_integral
#print axioms C1T15_palette

theorem C1T16_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T16_den) :
    C1T16.Integral p :=
  FibreCert.integral_of_denOk C1T16 C1T16_den p C1T16_den_ok hp

theorem C1T16_palette :
    (∀ d ∈ C1T16.R, C1T16.lf d = poleL 1 0 d ∧ C1T16.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T16.C, C1T16.lf d = poleL 1 0 d ∧ C1T16.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T16_integral
#print axioms C1T16_palette

theorem C1T17_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T17_den) :
    C1T17.Integral p :=
  FibreCert.integral_of_denOk C1T17 C1T17_den p C1T17_den_ok hp

theorem C1T17_palette :
    (∀ d ∈ C1T17.R, C1T17.lf d = poleL 1 1 d ∧ C1T17.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T17.C, C1T17.lf d = poleL 1 1 d ∧ C1T17.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T17_integral
#print axioms C1T17_palette

theorem C1T18_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T18_den) :
    C1T18.Integral p :=
  FibreCert.integral_of_denOk C1T18 C1T18_den p C1T18_den_ok hp

theorem C1T18_palette :
    (∀ d ∈ C1T18.R, C1T18.lf d = poleL 1 1 d ∧ C1T18.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T18.C, C1T18.lf d = poleL 1 1 d ∧ C1T18.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T18_integral
#print axioms C1T18_palette

theorem C1T19_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T19_den) :
    C1T19.Integral p :=
  FibreCert.integral_of_denOk C1T19 C1T19_den p C1T19_den_ok hp

theorem C1T19_palette :
    (∀ d ∈ C1T19.R, C1T19.lf d = poleL 1 0 d ∧ C1T19.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T19.C, C1T19.lf d = poleL 1 0 d ∧ C1T19.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T19_integral
#print axioms C1T19_palette

theorem C1T20_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T20_den) :
    C1T20.Integral p :=
  FibreCert.integral_of_denOk C1T20 C1T20_den p C1T20_den_ok hp

theorem C1T20_palette :
    (∀ d ∈ C1T20.R, C1T20.lf d = poleL 1 1 d ∧ C1T20.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T20.C, C1T20.lf d = poleL 1 1 d ∧ C1T20.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T20_integral
#print axioms C1T20_palette

theorem C1T21_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T21_den) :
    C1T21.Integral p :=
  FibreCert.integral_of_denOk C1T21 C1T21_den p C1T21_den_ok hp

theorem C1T21_palette :
    (∀ d ∈ C1T21.R, C1T21.lf d = poleL 1 0 d ∧ C1T21.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T21.C, C1T21.lf d = poleL 1 0 d ∧ C1T21.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T21_integral
#print axioms C1T21_palette

theorem C1T22_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T22_den) :
    C1T22.Integral p :=
  FibreCert.integral_of_denOk C1T22 C1T22_den p C1T22_den_ok hp

theorem C1T22_palette :
    (∀ d ∈ C1T22.R, C1T22.lf d = poleL 1 0 d ∧ C1T22.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T22.C, C1T22.lf d = poleL 1 0 d ∧ C1T22.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T22_integral
#print axioms C1T22_palette

theorem C1T23_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T23_den) :
    C1T23.Integral p :=
  FibreCert.integral_of_denOk C1T23 C1T23_den p C1T23_den_ok hp

theorem C1T23_palette :
    (∀ d ∈ C1T23.R, C1T23.lf d = poleL 1 1 d ∧ C1T23.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T23.C, C1T23.lf d = poleL 1 1 d ∧ C1T23.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T23_integral
#print axioms C1T23_palette

theorem C1T24_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T24_den) :
    C1T24.Integral p :=
  FibreCert.integral_of_denOk C1T24 C1T24_den p C1T24_den_ok hp

theorem C1T24_palette :
    (∀ d ∈ C1T24.R, C1T24.lf d = poleL 1 1 d ∧ C1T24.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T24.C, C1T24.lf d = poleL 1 1 d ∧ C1T24.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T24_integral
#print axioms C1T24_palette

theorem C1T25_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T25_den) :
    C1T25.Integral p :=
  FibreCert.integral_of_denOk C1T25 C1T25_den p C1T25_den_ok hp

theorem C1T25_palette :
    (∀ d ∈ C1T25.R, C1T25.lf d = poleL 1 0 d ∧ C1T25.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T25.C, C1T25.lf d = poleL 1 0 d ∧ C1T25.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T25_integral
#print axioms C1T25_palette

theorem C1T26_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T26_den) :
    C1T26.Integral p :=
  FibreCert.integral_of_denOk C1T26 C1T26_den p C1T26_den_ok hp

theorem C1T26_palette :
    (∀ d ∈ C1T26.R, C1T26.lf d = poleL 1 1 d ∧ C1T26.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T26.C, C1T26.lf d = poleL 1 1 d ∧ C1T26.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T26_integral
#print axioms C1T26_palette

theorem C1T27_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T27_den) :
    C1T27.Integral p :=
  FibreCert.integral_of_denOk C1T27 C1T27_den p C1T27_den_ok hp

theorem C1T27_palette :
    (∀ d ∈ C1T27.R, C1T27.lf d = poleL 1 0 d ∧ C1T27.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T27.C, C1T27.lf d = poleL 1 0 d ∧ C1T27.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T27_integral
#print axioms C1T27_palette

theorem C1T28_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T28_den) :
    C1T28.Integral p :=
  FibreCert.integral_of_denOk C1T28 C1T28_den p C1T28_den_ok hp

theorem C1T28_palette :
    (∀ d ∈ C1T28.R, C1T28.lf d = poleL 1 0 d ∧ C1T28.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T28.C, C1T28.lf d = poleL 1 0 d ∧ C1T28.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T28_integral
#print axioms C1T28_palette

theorem C1T29_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T29_den) :
    C1T29.Integral p :=
  FibreCert.integral_of_denOk C1T29 C1T29_den p C1T29_den_ok hp

theorem C1T29_palette :
    (∀ d ∈ C1T29.R, C1T29.lf d = poleL 1 1 d ∧ C1T29.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T29.C, C1T29.lf d = poleL 1 1 d ∧ C1T29.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T29_integral
#print axioms C1T29_palette

theorem C1T30_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T30_den) :
    C1T30.Integral p :=
  FibreCert.integral_of_denOk C1T30 C1T30_den p C1T30_den_ok hp

theorem C1T30_palette :
    (∀ d ∈ C1T30.R, C1T30.lf d = poleL 1 1 d ∧ C1T30.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T30.C, C1T30.lf d = poleL 1 1 d ∧ C1T30.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T30_integral
#print axioms C1T30_palette

theorem C1T31_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T31_den) :
    C1T31.Integral p :=
  FibreCert.integral_of_denOk C1T31 C1T31_den p C1T31_den_ok hp

theorem C1T31_palette :
    (∀ d ∈ C1T31.R, C1T31.lf d = poleL 1 0 d ∧ C1T31.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T31.C, C1T31.lf d = poleL 1 0 d ∧ C1T31.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T31_integral
#print axioms C1T31_palette

theorem C1T32_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T32_den) :
    C1T32.Integral p :=
  FibreCert.integral_of_denOk C1T32 C1T32_den p C1T32_den_ok hp

theorem C1T32_palette :
    (∀ d ∈ C1T32.R, C1T32.lf d = poleL 1 1 d ∧ C1T32.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T32.C, C1T32.lf d = poleL 1 1 d ∧ C1T32.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T32_integral
#print axioms C1T32_palette

theorem C1T33_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T33_den) :
    C1T33.Integral p :=
  FibreCert.integral_of_denOk C1T33 C1T33_den p C1T33_den_ok hp

theorem C1T33_palette :
    (∀ d ∈ C1T33.R, C1T33.lf d = poleL 1 0 d ∧ C1T33.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T33.C, C1T33.lf d = poleL 1 0 d ∧ C1T33.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T33_integral
#print axioms C1T33_palette

theorem C1T34_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T34_den) :
    C1T34.Integral p :=
  FibreCert.integral_of_denOk C1T34 C1T34_den p C1T34_den_ok hp

theorem C1T34_palette :
    (∀ d ∈ C1T34.R, C1T34.lf d = poleL 1 0 d ∧ C1T34.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T34.C, C1T34.lf d = poleL 1 0 d ∧ C1T34.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T34_integral
#print axioms C1T34_palette

theorem C1T35_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T35_den) :
    C1T35.Integral p :=
  FibreCert.integral_of_denOk C1T35 C1T35_den p C1T35_den_ok hp

theorem C1T35_palette :
    (∀ d ∈ C1T35.R, C1T35.lf d = poleL 1 1 d ∧ C1T35.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T35.C, C1T35.lf d = poleL 1 1 d ∧ C1T35.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T35_integral
#print axioms C1T35_palette

theorem C1T36_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T36_den) :
    C1T36.Integral p :=
  FibreCert.integral_of_denOk C1T36 C1T36_den p C1T36_den_ok hp

theorem C1T36_palette :
    (∀ d ∈ C1T36.R, C1T36.lf d = poleL 1 1 d ∧ C1T36.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T36.C, C1T36.lf d = poleL 1 1 d ∧ C1T36.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel

#print axioms C1T36_integral
#print axioms C1T36_palette

theorem C1T37_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T37_den) :
    C1T37.Integral p :=
  FibreCert.integral_of_denOk C1T37 C1T37_den p C1T37_den_ok hp

theorem C1T37_palette :
    (∀ d ∈ C1T37.R, C1T37.lf d = poleL 1 0 d ∧ C1T37.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T37.C, C1T37.lf d = poleL 1 0 d ∧ C1T37.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T37_integral
#print axioms C1T37_palette

theorem C1T38_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T38_den) :
    C1T38.Integral p :=
  FibreCert.integral_of_denOk C1T38 C1T38_den p C1T38_den_ok hp

theorem C1T38_palette :
    (∀ d ∈ C1T38.R, C1T38.lf d = poleL 1 0 d ∧ C1T38.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T38.C, C1T38.lf d = poleL 1 0 d ∧ C1T38.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T38_integral
#print axioms C1T38_palette

theorem C1T39_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T39_den) :
    C1T39.Integral p :=
  FibreCert.integral_of_denOk C1T39 C1T39_den p C1T39_den_ok hp

theorem C1T39_palette :
    (∀ d ∈ C1T39.R, C1T39.lf d = poleL 1 0 d ∧ C1T39.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T39.C, C1T39.lf d = poleL 1 0 d ∧ C1T39.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel

#print axioms C1T39_integral
#print axioms C1T39_palette

end CatalanCore.Uniform.Bank.Sevenths.RankData
