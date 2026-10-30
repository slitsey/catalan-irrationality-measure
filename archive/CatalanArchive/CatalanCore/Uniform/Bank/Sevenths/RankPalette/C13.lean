import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C13
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer
theorem C13T00_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T00_den) :
    C13T00.Integral p :=
  FibreCert.integral_of_denOk C13T00 C13T00_den p C13T00_den_ok hp

theorem C13T00_palette :
    (∀ d ∈ C13T00.R, C13T00.lf d = poleL 6 0 d ∧ C13T00.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T00.C, C13T00.lf d = poleL 6 0 d ∧ C13T00.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T00_integral
#print axioms C13T00_palette

theorem C13T01_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T01_den) :
    C13T01.Integral p :=
  FibreCert.integral_of_denOk C13T01 C13T01_den p C13T01_den_ok hp

theorem C13T01_palette :
    (∀ d ∈ C13T01.R, C13T01.lf d = poleL 6 0 d ∧ C13T01.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T01.C, C13T01.lf d = poleL 6 0 d ∧ C13T01.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T01_integral
#print axioms C13T01_palette

theorem C13T02_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T02_den) :
    C13T02.Integral p :=
  FibreCert.integral_of_denOk C13T02 C13T02_den p C13T02_den_ok hp

theorem C13T02_palette :
    (∀ d ∈ C13T02.R, C13T02.lf d = poleL 6 1 d ∧ C13T02.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T02.C, C13T02.lf d = poleL 6 1 d ∧ C13T02.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T02_integral
#print axioms C13T02_palette

theorem C13T03_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T03_den) :
    C13T03.Integral p :=
  FibreCert.integral_of_denOk C13T03 C13T03_den p C13T03_den_ok hp

theorem C13T03_palette :
    (∀ d ∈ C13T03.R, C13T03.lf d = poleL 6 1 d ∧ C13T03.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T03.C, C13T03.lf d = poleL 6 1 d ∧ C13T03.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T03_integral
#print axioms C13T03_palette

theorem C13T04_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T04_den) :
    C13T04.Integral p :=
  FibreCert.integral_of_denOk C13T04 C13T04_den p C13T04_den_ok hp

theorem C13T04_palette :
    (∀ d ∈ C13T04.R, C13T04.lf d = poleL 6 1 d ∧ C13T04.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T04.C, C13T04.lf d = poleL 6 1 d ∧ C13T04.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T04_integral
#print axioms C13T04_palette

theorem C13T05_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T05_den) :
    C13T05.Integral p :=
  FibreCert.integral_of_denOk C13T05 C13T05_den p C13T05_den_ok hp

theorem C13T05_palette :
    (∀ d ∈ C13T05.R, C13T05.lf d = poleL 6 1 d ∧ C13T05.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T05.C, C13T05.lf d = poleL 6 1 d ∧ C13T05.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T05_integral
#print axioms C13T05_palette

theorem C13T06_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T06_den) :
    C13T06.Integral p :=
  FibreCert.integral_of_denOk C13T06 C13T06_den p C13T06_den_ok hp

theorem C13T06_palette :
    (∀ d ∈ C13T06.R, C13T06.lf d = poleL 6 1 d ∧ C13T06.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T06.C, C13T06.lf d = poleL 6 1 d ∧ C13T06.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T06_integral
#print axioms C13T06_palette

theorem C13T07_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T07_den) :
    C13T07.Integral p :=
  FibreCert.integral_of_denOk C13T07 C13T07_den p C13T07_den_ok hp

theorem C13T07_palette :
    (∀ d ∈ C13T07.R, C13T07.lf d = poleL 6 0 d ∧ C13T07.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T07.C, C13T07.lf d = poleL 6 0 d ∧ C13T07.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T07_integral
#print axioms C13T07_palette

theorem C13T08_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T08_den) :
    C13T08.Integral p :=
  FibreCert.integral_of_denOk C13T08 C13T08_den p C13T08_den_ok hp

theorem C13T08_palette :
    (∀ d ∈ C13T08.R, C13T08.lf d = poleL 6 0 d ∧ C13T08.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T08.C, C13T08.lf d = poleL 6 0 d ∧ C13T08.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T08_integral
#print axioms C13T08_palette

theorem C13T09_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T09_den) :
    C13T09.Integral p :=
  FibreCert.integral_of_denOk C13T09 C13T09_den p C13T09_den_ok hp

theorem C13T09_palette :
    (∀ d ∈ C13T09.R, C13T09.lf d = poleL 6 0 d ∧ C13T09.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T09.C, C13T09.lf d = poleL 6 0 d ∧ C13T09.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T09_integral
#print axioms C13T09_palette

theorem C13T10_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T10_den) :
    C13T10.Integral p :=
  FibreCert.integral_of_denOk C13T10 C13T10_den p C13T10_den_ok hp

theorem C13T10_palette :
    (∀ d ∈ C13T10.R, C13T10.lf d = poleL 6 1 d ∧ C13T10.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T10.C, C13T10.lf d = poleL 6 1 d ∧ C13T10.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T10_integral
#print axioms C13T10_palette

theorem C13T11_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T11_den) :
    C13T11.Integral p :=
  FibreCert.integral_of_denOk C13T11 C13T11_den p C13T11_den_ok hp

theorem C13T11_palette :
    (∀ d ∈ C13T11.R, C13T11.lf d = poleL 6 0 d ∧ C13T11.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T11.C, C13T11.lf d = poleL 6 0 d ∧ C13T11.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T11_integral
#print axioms C13T11_palette

theorem C13T12_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T12_den) :
    C13T12.Integral p :=
  FibreCert.integral_of_denOk C13T12 C13T12_den p C13T12_den_ok hp

theorem C13T12_palette :
    (∀ d ∈ C13T12.R, C13T12.lf d = poleL 6 1 d ∧ C13T12.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T12.C, C13T12.lf d = poleL 6 1 d ∧ C13T12.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T12_integral
#print axioms C13T12_palette

theorem C13T13_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T13_den) :
    C13T13.Integral p :=
  FibreCert.integral_of_denOk C13T13 C13T13_den p C13T13_den_ok hp

theorem C13T13_palette :
    (∀ d ∈ C13T13.R, C13T13.lf d = poleL 6 1 d ∧ C13T13.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T13.C, C13T13.lf d = poleL 6 1 d ∧ C13T13.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T13_integral
#print axioms C13T13_palette

theorem C13T14_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T14_den) :
    C13T14.Integral p :=
  FibreCert.integral_of_denOk C13T14 C13T14_den p C13T14_den_ok hp

theorem C13T14_palette :
    (∀ d ∈ C13T14.R, C13T14.lf d = poleL 6 0 d ∧ C13T14.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T14.C, C13T14.lf d = poleL 6 0 d ∧ C13T14.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T14_integral
#print axioms C13T14_palette

theorem C13T15_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T15_den) :
    C13T15.Integral p :=
  FibreCert.integral_of_denOk C13T15 C13T15_den p C13T15_den_ok hp

theorem C13T15_palette :
    (∀ d ∈ C13T15.R, C13T15.lf d = poleL 6 0 d ∧ C13T15.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T15.C, C13T15.lf d = poleL 6 0 d ∧ C13T15.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T15_integral
#print axioms C13T15_palette

theorem C13T16_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T16_den) :
    C13T16.Integral p :=
  FibreCert.integral_of_denOk C13T16 C13T16_den p C13T16_den_ok hp

theorem C13T16_palette :
    (∀ d ∈ C13T16.R, C13T16.lf d = poleL 6 1 d ∧ C13T16.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T16.C, C13T16.lf d = poleL 6 1 d ∧ C13T16.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T16_integral
#print axioms C13T16_palette

theorem C13T17_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T17_den) :
    C13T17.Integral p :=
  FibreCert.integral_of_denOk C13T17 C13T17_den p C13T17_den_ok hp

theorem C13T17_palette :
    (∀ d ∈ C13T17.R, C13T17.lf d = poleL 6 0 d ∧ C13T17.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T17.C, C13T17.lf d = poleL 6 0 d ∧ C13T17.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T17_integral
#print axioms C13T17_palette

theorem C13T18_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T18_den) :
    C13T18.Integral p :=
  FibreCert.integral_of_denOk C13T18 C13T18_den p C13T18_den_ok hp

theorem C13T18_palette :
    (∀ d ∈ C13T18.R, C13T18.lf d = poleL 6 1 d ∧ C13T18.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T18.C, C13T18.lf d = poleL 6 1 d ∧ C13T18.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T18_integral
#print axioms C13T18_palette

theorem C13T19_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T19_den) :
    C13T19.Integral p :=
  FibreCert.integral_of_denOk C13T19 C13T19_den p C13T19_den_ok hp

theorem C13T19_palette :
    (∀ d ∈ C13T19.R, C13T19.lf d = poleL 6 1 d ∧ C13T19.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T19.C, C13T19.lf d = poleL 6 1 d ∧ C13T19.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T19_integral
#print axioms C13T19_palette

theorem C13T20_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T20_den) :
    C13T20.Integral p :=
  FibreCert.integral_of_denOk C13T20 C13T20_den p C13T20_den_ok hp

theorem C13T20_palette :
    (∀ d ∈ C13T20.R, C13T20.lf d = poleL 6 0 d ∧ C13T20.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T20.C, C13T20.lf d = poleL 6 0 d ∧ C13T20.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T20_integral
#print axioms C13T20_palette

theorem C13T21_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T21_den) :
    C13T21.Integral p :=
  FibreCert.integral_of_denOk C13T21 C13T21_den p C13T21_den_ok hp

theorem C13T21_palette :
    (∀ d ∈ C13T21.R, C13T21.lf d = poleL 6 0 d ∧ C13T21.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T21.C, C13T21.lf d = poleL 6 0 d ∧ C13T21.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T21_integral
#print axioms C13T21_palette

theorem C13T22_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T22_den) :
    C13T22.Integral p :=
  FibreCert.integral_of_denOk C13T22 C13T22_den p C13T22_den_ok hp

theorem C13T22_palette :
    (∀ d ∈ C13T22.R, C13T22.lf d = poleL 6 1 d ∧ C13T22.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T22.C, C13T22.lf d = poleL 6 1 d ∧ C13T22.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T22_integral
#print axioms C13T22_palette

theorem C13T23_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T23_den) :
    C13T23.Integral p :=
  FibreCert.integral_of_denOk C13T23 C13T23_den p C13T23_den_ok hp

theorem C13T23_palette :
    (∀ d ∈ C13T23.R, C13T23.lf d = poleL 6 0 d ∧ C13T23.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T23.C, C13T23.lf d = poleL 6 0 d ∧ C13T23.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T23_integral
#print axioms C13T23_palette

theorem C13T24_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T24_den) :
    C13T24.Integral p :=
  FibreCert.integral_of_denOk C13T24 C13T24_den p C13T24_den_ok hp

theorem C13T24_palette :
    (∀ d ∈ C13T24.R, C13T24.lf d = poleL 6 1 d ∧ C13T24.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T24.C, C13T24.lf d = poleL 6 1 d ∧ C13T24.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T24_integral
#print axioms C13T24_palette

theorem C13T25_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T25_den) :
    C13T25.Integral p :=
  FibreCert.integral_of_denOk C13T25 C13T25_den p C13T25_den_ok hp

theorem C13T25_palette :
    (∀ d ∈ C13T25.R, C13T25.lf d = poleL 6 1 d ∧ C13T25.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T25.C, C13T25.lf d = poleL 6 1 d ∧ C13T25.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T25_integral
#print axioms C13T25_palette

theorem C13T26_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T26_den) :
    C13T26.Integral p :=
  FibreCert.integral_of_denOk C13T26 C13T26_den p C13T26_den_ok hp

theorem C13T26_palette :
    (∀ d ∈ C13T26.R, C13T26.lf d = poleL 6 0 d ∧ C13T26.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T26.C, C13T26.lf d = poleL 6 0 d ∧ C13T26.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T26_integral
#print axioms C13T26_palette

theorem C13T27_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T27_den) :
    C13T27.Integral p :=
  FibreCert.integral_of_denOk C13T27 C13T27_den p C13T27_den_ok hp

theorem C13T27_palette :
    (∀ d ∈ C13T27.R, C13T27.lf d = poleL 6 0 d ∧ C13T27.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T27.C, C13T27.lf d = poleL 6 0 d ∧ C13T27.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T27_integral
#print axioms C13T27_palette

theorem C13T28_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T28_den) :
    C13T28.Integral p :=
  FibreCert.integral_of_denOk C13T28 C13T28_den p C13T28_den_ok hp

theorem C13T28_palette :
    (∀ d ∈ C13T28.R, C13T28.lf d = poleL 6 1 d ∧ C13T28.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T28.C, C13T28.lf d = poleL 6 1 d ∧ C13T28.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T28_integral
#print axioms C13T28_palette

theorem C13T29_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T29_den) :
    C13T29.Integral p :=
  FibreCert.integral_of_denOk C13T29 C13T29_den p C13T29_den_ok hp

theorem C13T29_palette :
    (∀ d ∈ C13T29.R, C13T29.lf d = poleL 6 0 d ∧ C13T29.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T29.C, C13T29.lf d = poleL 6 0 d ∧ C13T29.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T29_integral
#print axioms C13T29_palette

theorem C13T30_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T30_den) :
    C13T30.Integral p :=
  FibreCert.integral_of_denOk C13T30 C13T30_den p C13T30_den_ok hp

theorem C13T30_palette :
    (∀ d ∈ C13T30.R, C13T30.lf d = poleL 6 1 d ∧ C13T30.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T30.C, C13T30.lf d = poleL 6 1 d ∧ C13T30.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T30_integral
#print axioms C13T30_palette

theorem C13T31_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T31_den) :
    C13T31.Integral p :=
  FibreCert.integral_of_denOk C13T31 C13T31_den p C13T31_den_ok hp

theorem C13T31_palette :
    (∀ d ∈ C13T31.R, C13T31.lf d = poleL 6 1 d ∧ C13T31.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T31.C, C13T31.lf d = poleL 6 1 d ∧ C13T31.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T31_integral
#print axioms C13T31_palette

theorem C13T32_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T32_den) :
    C13T32.Integral p :=
  FibreCert.integral_of_denOk C13T32 C13T32_den p C13T32_den_ok hp

theorem C13T32_palette :
    (∀ d ∈ C13T32.R, C13T32.lf d = poleL 6 0 d ∧ C13T32.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T32.C, C13T32.lf d = poleL 6 0 d ∧ C13T32.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T32_integral
#print axioms C13T32_palette

theorem C13T33_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T33_den) :
    C13T33.Integral p :=
  FibreCert.integral_of_denOk C13T33 C13T33_den p C13T33_den_ok hp

theorem C13T33_palette :
    (∀ d ∈ C13T33.R, C13T33.lf d = poleL 6 0 d ∧ C13T33.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T33.C, C13T33.lf d = poleL 6 0 d ∧ C13T33.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T33_integral
#print axioms C13T33_palette

theorem C13T34_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T34_den) :
    C13T34.Integral p :=
  FibreCert.integral_of_denOk C13T34 C13T34_den p C13T34_den_ok hp

theorem C13T34_palette :
    (∀ d ∈ C13T34.R, C13T34.lf d = poleL 6 1 d ∧ C13T34.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T34.C, C13T34.lf d = poleL 6 1 d ∧ C13T34.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T34_integral
#print axioms C13T34_palette

theorem C13T35_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T35_den) :
    C13T35.Integral p :=
  FibreCert.integral_of_denOk C13T35 C13T35_den p C13T35_den_ok hp

theorem C13T35_palette :
    (∀ d ∈ C13T35.R, C13T35.lf d = poleL 6 0 d ∧ C13T35.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T35.C, C13T35.lf d = poleL 6 0 d ∧ C13T35.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T35_integral
#print axioms C13T35_palette

theorem C13T36_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T36_den) :
    C13T36.Integral p :=
  FibreCert.integral_of_denOk C13T36 C13T36_den p C13T36_den_ok hp

theorem C13T36_palette :
    (∀ d ∈ C13T36.R, C13T36.lf d = poleL 6 1 d ∧ C13T36.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T36.C, C13T36.lf d = poleL 6 1 d ∧ C13T36.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T36_integral
#print axioms C13T36_palette

theorem C13T37_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T37_den) :
    C13T37.Integral p :=
  FibreCert.integral_of_denOk C13T37 C13T37_den p C13T37_den_ok hp

theorem C13T37_palette :
    (∀ d ∈ C13T37.R, C13T37.lf d = poleL 6 1 d ∧ C13T37.ee d = poleE 6 1 d) ∧
    (∀ d ∈ C13T37.C, C13T37.lf d = poleL 6 1 d ∧ C13T37.ee d = poleE 6 1 d) := by
  constructor <;> decide +kernel

#print axioms C13T37_integral
#print axioms C13T37_palette

theorem C13T38_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T38_den) :
    C13T38.Integral p :=
  FibreCert.integral_of_denOk C13T38 C13T38_den p C13T38_den_ok hp

theorem C13T38_palette :
    (∀ d ∈ C13T38.R, C13T38.lf d = poleL 6 0 d ∧ C13T38.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T38.C, C13T38.lf d = poleL 6 0 d ∧ C13T38.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T38_integral
#print axioms C13T38_palette

theorem C13T39_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C13T39_den) :
    C13T39.Integral p :=
  FibreCert.integral_of_denOk C13T39 C13T39_den p C13T39_den_ok hp

theorem C13T39_palette :
    (∀ d ∈ C13T39.R, C13T39.lf d = poleL 6 0 d ∧ C13T39.ee d = poleE 6 0 d) ∧
    (∀ d ∈ C13T39.C, C13T39.lf d = poleL 6 0 d ∧ C13T39.ee d = poleE 6 0 d) := by
  constructor <;> decide +kernel

#print axioms C13T39_integral
#print axioms C13T39_palette

end CatalanCore.Uniform.Bank.Sevenths.RankData
