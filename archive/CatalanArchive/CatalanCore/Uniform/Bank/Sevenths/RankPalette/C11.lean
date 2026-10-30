import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C11
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer
theorem C11T00_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T00_den) :
    C11T00.Integral p :=
  FibreCert.integral_of_denOk C11T00 C11T00_den p C11T00_den_ok hp

theorem C11T00_palette :
    (∀ d ∈ C11T00.R, C11T00.lf d = poleL 2 0 d ∧ C11T00.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T00.C, C11T00.lf d = poleL 2 0 d ∧ C11T00.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T00_integral
#print axioms C11T00_palette

theorem C11T01_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T01_den) :
    C11T01.Integral p :=
  FibreCert.integral_of_denOk C11T01 C11T01_den p C11T01_den_ok hp

theorem C11T01_palette :
    (∀ d ∈ C11T01.R, C11T01.lf d = poleL 2 0 d ∧ C11T01.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T01.C, C11T01.lf d = poleL 2 0 d ∧ C11T01.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T01_integral
#print axioms C11T01_palette

theorem C11T02_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T02_den) :
    C11T02.Integral p :=
  FibreCert.integral_of_denOk C11T02 C11T02_den p C11T02_den_ok hp

theorem C11T02_palette :
    (∀ d ∈ C11T02.R, C11T02.lf d = poleL 2 1 d ∧ C11T02.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T02.C, C11T02.lf d = poleL 2 1 d ∧ C11T02.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T02_integral
#print axioms C11T02_palette

theorem C11T03_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T03_den) :
    C11T03.Integral p :=
  FibreCert.integral_of_denOk C11T03 C11T03_den p C11T03_den_ok hp

theorem C11T03_palette :
    (∀ d ∈ C11T03.R, C11T03.lf d = poleL 2 1 d ∧ C11T03.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T03.C, C11T03.lf d = poleL 2 1 d ∧ C11T03.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T03_integral
#print axioms C11T03_palette

theorem C11T04_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T04_den) :
    C11T04.Integral p :=
  FibreCert.integral_of_denOk C11T04 C11T04_den p C11T04_den_ok hp

theorem C11T04_palette :
    (∀ d ∈ C11T04.R, C11T04.lf d = poleL 2 1 d ∧ C11T04.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T04.C, C11T04.lf d = poleL 2 1 d ∧ C11T04.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T04_integral
#print axioms C11T04_palette

theorem C11T05_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T05_den) :
    C11T05.Integral p :=
  FibreCert.integral_of_denOk C11T05 C11T05_den p C11T05_den_ok hp

theorem C11T05_palette :
    (∀ d ∈ C11T05.R, C11T05.lf d = poleL 2 1 d ∧ C11T05.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T05.C, C11T05.lf d = poleL 2 1 d ∧ C11T05.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T05_integral
#print axioms C11T05_palette

theorem C11T06_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T06_den) :
    C11T06.Integral p :=
  FibreCert.integral_of_denOk C11T06 C11T06_den p C11T06_den_ok hp

theorem C11T06_palette :
    (∀ d ∈ C11T06.R, C11T06.lf d = poleL 2 1 d ∧ C11T06.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T06.C, C11T06.lf d = poleL 2 1 d ∧ C11T06.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T06_integral
#print axioms C11T06_palette

theorem C11T07_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T07_den) :
    C11T07.Integral p :=
  FibreCert.integral_of_denOk C11T07 C11T07_den p C11T07_den_ok hp

theorem C11T07_palette :
    (∀ d ∈ C11T07.R, C11T07.lf d = poleL 2 0 d ∧ C11T07.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T07.C, C11T07.lf d = poleL 2 0 d ∧ C11T07.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T07_integral
#print axioms C11T07_palette

theorem C11T08_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T08_den) :
    C11T08.Integral p :=
  FibreCert.integral_of_denOk C11T08 C11T08_den p C11T08_den_ok hp

theorem C11T08_palette :
    (∀ d ∈ C11T08.R, C11T08.lf d = poleL 2 0 d ∧ C11T08.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T08.C, C11T08.lf d = poleL 2 0 d ∧ C11T08.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T08_integral
#print axioms C11T08_palette

theorem C11T09_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T09_den) :
    C11T09.Integral p :=
  FibreCert.integral_of_denOk C11T09 C11T09_den p C11T09_den_ok hp

theorem C11T09_palette :
    (∀ d ∈ C11T09.R, C11T09.lf d = poleL 2 0 d ∧ C11T09.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T09.C, C11T09.lf d = poleL 2 0 d ∧ C11T09.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T09_integral
#print axioms C11T09_palette

theorem C11T10_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T10_den) :
    C11T10.Integral p :=
  FibreCert.integral_of_denOk C11T10 C11T10_den p C11T10_den_ok hp

theorem C11T10_palette :
    (∀ d ∈ C11T10.R, C11T10.lf d = poleL 2 1 d ∧ C11T10.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T10.C, C11T10.lf d = poleL 2 1 d ∧ C11T10.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T10_integral
#print axioms C11T10_palette

theorem C11T11_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T11_den) :
    C11T11.Integral p :=
  FibreCert.integral_of_denOk C11T11 C11T11_den p C11T11_den_ok hp

theorem C11T11_palette :
    (∀ d ∈ C11T11.R, C11T11.lf d = poleL 2 1 d ∧ C11T11.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T11.C, C11T11.lf d = poleL 2 1 d ∧ C11T11.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T11_integral
#print axioms C11T11_palette

theorem C11T12_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T12_den) :
    C11T12.Integral p :=
  FibreCert.integral_of_denOk C11T12 C11T12_den p C11T12_den_ok hp

theorem C11T12_palette :
    (∀ d ∈ C11T12.R, C11T12.lf d = poleL 2 1 d ∧ C11T12.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T12.C, C11T12.lf d = poleL 2 1 d ∧ C11T12.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T12_integral
#print axioms C11T12_palette

theorem C11T13_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T13_den) :
    C11T13.Integral p :=
  FibreCert.integral_of_denOk C11T13 C11T13_den p C11T13_den_ok hp

theorem C11T13_palette :
    (∀ d ∈ C11T13.R, C11T13.lf d = poleL 2 0 d ∧ C11T13.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T13.C, C11T13.lf d = poleL 2 0 d ∧ C11T13.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T13_integral
#print axioms C11T13_palette

theorem C11T14_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T14_den) :
    C11T14.Integral p :=
  FibreCert.integral_of_denOk C11T14 C11T14_den p C11T14_den_ok hp

theorem C11T14_palette :
    (∀ d ∈ C11T14.R, C11T14.lf d = poleL 2 0 d ∧ C11T14.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T14.C, C11T14.lf d = poleL 2 0 d ∧ C11T14.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T14_integral
#print axioms C11T14_palette

theorem C11T15_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T15_den) :
    C11T15.Integral p :=
  FibreCert.integral_of_denOk C11T15 C11T15_den p C11T15_den_ok hp

theorem C11T15_palette :
    (∀ d ∈ C11T15.R, C11T15.lf d = poleL 2 0 d ∧ C11T15.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T15.C, C11T15.lf d = poleL 2 0 d ∧ C11T15.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T15_integral
#print axioms C11T15_palette

theorem C11T16_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T16_den) :
    C11T16.Integral p :=
  FibreCert.integral_of_denOk C11T16 C11T16_den p C11T16_den_ok hp

theorem C11T16_palette :
    (∀ d ∈ C11T16.R, C11T16.lf d = poleL 2 1 d ∧ C11T16.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T16.C, C11T16.lf d = poleL 2 1 d ∧ C11T16.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T16_integral
#print axioms C11T16_palette

theorem C11T17_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T17_den) :
    C11T17.Integral p :=
  FibreCert.integral_of_denOk C11T17 C11T17_den p C11T17_den_ok hp

theorem C11T17_palette :
    (∀ d ∈ C11T17.R, C11T17.lf d = poleL 2 1 d ∧ C11T17.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T17.C, C11T17.lf d = poleL 2 1 d ∧ C11T17.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T17_integral
#print axioms C11T17_palette

theorem C11T18_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T18_den) :
    C11T18.Integral p :=
  FibreCert.integral_of_denOk C11T18 C11T18_den p C11T18_den_ok hp

theorem C11T18_palette :
    (∀ d ∈ C11T18.R, C11T18.lf d = poleL 2 1 d ∧ C11T18.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T18.C, C11T18.lf d = poleL 2 1 d ∧ C11T18.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T18_integral
#print axioms C11T18_palette

theorem C11T19_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T19_den) :
    C11T19.Integral p :=
  FibreCert.integral_of_denOk C11T19 C11T19_den p C11T19_den_ok hp

theorem C11T19_palette :
    (∀ d ∈ C11T19.R, C11T19.lf d = poleL 2 0 d ∧ C11T19.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T19.C, C11T19.lf d = poleL 2 0 d ∧ C11T19.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T19_integral
#print axioms C11T19_palette

theorem C11T20_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T20_den) :
    C11T20.Integral p :=
  FibreCert.integral_of_denOk C11T20 C11T20_den p C11T20_den_ok hp

theorem C11T20_palette :
    (∀ d ∈ C11T20.R, C11T20.lf d = poleL 2 1 d ∧ C11T20.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T20.C, C11T20.lf d = poleL 2 1 d ∧ C11T20.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T20_integral
#print axioms C11T20_palette

theorem C11T21_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T21_den) :
    C11T21.Integral p :=
  FibreCert.integral_of_denOk C11T21 C11T21_den p C11T21_den_ok hp

theorem C11T21_palette :
    (∀ d ∈ C11T21.R, C11T21.lf d = poleL 2 0 d ∧ C11T21.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T21.C, C11T21.lf d = poleL 2 0 d ∧ C11T21.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T21_integral
#print axioms C11T21_palette

theorem C11T22_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T22_den) :
    C11T22.Integral p :=
  FibreCert.integral_of_denOk C11T22 C11T22_den p C11T22_den_ok hp

theorem C11T22_palette :
    (∀ d ∈ C11T22.R, C11T22.lf d = poleL 2 0 d ∧ C11T22.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T22.C, C11T22.lf d = poleL 2 0 d ∧ C11T22.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T22_integral
#print axioms C11T22_palette

theorem C11T23_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T23_den) :
    C11T23.Integral p :=
  FibreCert.integral_of_denOk C11T23 C11T23_den p C11T23_den_ok hp

theorem C11T23_palette :
    (∀ d ∈ C11T23.R, C11T23.lf d = poleL 2 1 d ∧ C11T23.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T23.C, C11T23.lf d = poleL 2 1 d ∧ C11T23.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T23_integral
#print axioms C11T23_palette

theorem C11T24_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T24_den) :
    C11T24.Integral p :=
  FibreCert.integral_of_denOk C11T24 C11T24_den p C11T24_den_ok hp

theorem C11T24_palette :
    (∀ d ∈ C11T24.R, C11T24.lf d = poleL 2 1 d ∧ C11T24.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T24.C, C11T24.lf d = poleL 2 1 d ∧ C11T24.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T24_integral
#print axioms C11T24_palette

theorem C11T25_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T25_den) :
    C11T25.Integral p :=
  FibreCert.integral_of_denOk C11T25 C11T25_den p C11T25_den_ok hp

theorem C11T25_palette :
    (∀ d ∈ C11T25.R, C11T25.lf d = poleL 2 0 d ∧ C11T25.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T25.C, C11T25.lf d = poleL 2 0 d ∧ C11T25.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T25_integral
#print axioms C11T25_palette

theorem C11T26_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T26_den) :
    C11T26.Integral p :=
  FibreCert.integral_of_denOk C11T26 C11T26_den p C11T26_den_ok hp

theorem C11T26_palette :
    (∀ d ∈ C11T26.R, C11T26.lf d = poleL 2 1 d ∧ C11T26.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T26.C, C11T26.lf d = poleL 2 1 d ∧ C11T26.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T26_integral
#print axioms C11T26_palette

theorem C11T27_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T27_den) :
    C11T27.Integral p :=
  FibreCert.integral_of_denOk C11T27 C11T27_den p C11T27_den_ok hp

theorem C11T27_palette :
    (∀ d ∈ C11T27.R, C11T27.lf d = poleL 2 0 d ∧ C11T27.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T27.C, C11T27.lf d = poleL 2 0 d ∧ C11T27.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T27_integral
#print axioms C11T27_palette

theorem C11T28_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T28_den) :
    C11T28.Integral p :=
  FibreCert.integral_of_denOk C11T28 C11T28_den p C11T28_den_ok hp

theorem C11T28_palette :
    (∀ d ∈ C11T28.R, C11T28.lf d = poleL 2 0 d ∧ C11T28.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T28.C, C11T28.lf d = poleL 2 0 d ∧ C11T28.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T28_integral
#print axioms C11T28_palette

theorem C11T29_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T29_den) :
    C11T29.Integral p :=
  FibreCert.integral_of_denOk C11T29 C11T29_den p C11T29_den_ok hp

theorem C11T29_palette :
    (∀ d ∈ C11T29.R, C11T29.lf d = poleL 2 1 d ∧ C11T29.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T29.C, C11T29.lf d = poleL 2 1 d ∧ C11T29.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T29_integral
#print axioms C11T29_palette

theorem C11T30_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T30_den) :
    C11T30.Integral p :=
  FibreCert.integral_of_denOk C11T30 C11T30_den p C11T30_den_ok hp

theorem C11T30_palette :
    (∀ d ∈ C11T30.R, C11T30.lf d = poleL 2 1 d ∧ C11T30.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T30.C, C11T30.lf d = poleL 2 1 d ∧ C11T30.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T30_integral
#print axioms C11T30_palette

theorem C11T31_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T31_den) :
    C11T31.Integral p :=
  FibreCert.integral_of_denOk C11T31 C11T31_den p C11T31_den_ok hp

theorem C11T31_palette :
    (∀ d ∈ C11T31.R, C11T31.lf d = poleL 2 0 d ∧ C11T31.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T31.C, C11T31.lf d = poleL 2 0 d ∧ C11T31.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T31_integral
#print axioms C11T31_palette

theorem C11T32_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T32_den) :
    C11T32.Integral p :=
  FibreCert.integral_of_denOk C11T32 C11T32_den p C11T32_den_ok hp

theorem C11T32_palette :
    (∀ d ∈ C11T32.R, C11T32.lf d = poleL 2 1 d ∧ C11T32.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T32.C, C11T32.lf d = poleL 2 1 d ∧ C11T32.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T32_integral
#print axioms C11T32_palette

theorem C11T33_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T33_den) :
    C11T33.Integral p :=
  FibreCert.integral_of_denOk C11T33 C11T33_den p C11T33_den_ok hp

theorem C11T33_palette :
    (∀ d ∈ C11T33.R, C11T33.lf d = poleL 2 0 d ∧ C11T33.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T33.C, C11T33.lf d = poleL 2 0 d ∧ C11T33.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T33_integral
#print axioms C11T33_palette

theorem C11T34_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T34_den) :
    C11T34.Integral p :=
  FibreCert.integral_of_denOk C11T34 C11T34_den p C11T34_den_ok hp

theorem C11T34_palette :
    (∀ d ∈ C11T34.R, C11T34.lf d = poleL 2 0 d ∧ C11T34.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T34.C, C11T34.lf d = poleL 2 0 d ∧ C11T34.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T34_integral
#print axioms C11T34_palette

theorem C11T35_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T35_den) :
    C11T35.Integral p :=
  FibreCert.integral_of_denOk C11T35 C11T35_den p C11T35_den_ok hp

theorem C11T35_palette :
    (∀ d ∈ C11T35.R, C11T35.lf d = poleL 2 0 d ∧ C11T35.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T35.C, C11T35.lf d = poleL 2 0 d ∧ C11T35.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T35_integral
#print axioms C11T35_palette

theorem C11T36_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T36_den) :
    C11T36.Integral p :=
  FibreCert.integral_of_denOk C11T36 C11T36_den p C11T36_den_ok hp

theorem C11T36_palette :
    (∀ d ∈ C11T36.R, C11T36.lf d = poleL 2 1 d ∧ C11T36.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T36.C, C11T36.lf d = poleL 2 1 d ∧ C11T36.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T36_integral
#print axioms C11T36_palette

theorem C11T37_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T37_den) :
    C11T37.Integral p :=
  FibreCert.integral_of_denOk C11T37 C11T37_den p C11T37_den_ok hp

theorem C11T37_palette :
    (∀ d ∈ C11T37.R, C11T37.lf d = poleL 2 1 d ∧ C11T37.ee d = poleE 2 1 d) ∧
    (∀ d ∈ C11T37.C, C11T37.lf d = poleL 2 1 d ∧ C11T37.ee d = poleE 2 1 d) := by
  constructor <;> decide +kernel

#print axioms C11T37_integral
#print axioms C11T37_palette

theorem C11T38_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T38_den) :
    C11T38.Integral p :=
  FibreCert.integral_of_denOk C11T38 C11T38_den p C11T38_den_ok hp

theorem C11T38_palette :
    (∀ d ∈ C11T38.R, C11T38.lf d = poleL 2 0 d ∧ C11T38.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T38.C, C11T38.lf d = poleL 2 0 d ∧ C11T38.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T38_integral
#print axioms C11T38_palette

theorem C11T39_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C11T39_den) :
    C11T39.Integral p :=
  FibreCert.integral_of_denOk C11T39 C11T39_den p C11T39_den_ok hp

theorem C11T39_palette :
    (∀ d ∈ C11T39.R, C11T39.lf d = poleL 2 0 d ∧ C11T39.ee d = poleE 2 0 d) ∧
    (∀ d ∈ C11T39.C, C11T39.lf d = poleL 2 0 d ∧ C11T39.ee d = poleE 2 0 d) := by
  constructor <;> decide +kernel

#print axioms C11T39_integral
#print axioms C11T39_palette

end CatalanCore.Uniform.Bank.Sevenths.RankData
