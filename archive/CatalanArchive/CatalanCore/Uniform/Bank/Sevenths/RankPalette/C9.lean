import CatalanCore.Uniform.Bank.Sevenths.PolePalette
import CatalanCore.Uniform.Content.RankProducer.Denominators
import CatalanCore.Uniform.Bank.Sevenths.RankData.C9
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore.Uniform.Content.RankProducer
theorem C9T00_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T00_den) :
    C9T00.Integral p :=
  FibreCert.integral_of_denOk C9T00 C9T00_den p C9T00_den_ok hp

theorem C9T00_palette :
    (∀ d ∈ C9T00.R, C9T00.lf d = poleL 4 0 d ∧ C9T00.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T00.C, C9T00.lf d = poleL 4 0 d ∧ C9T00.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T00_integral
#print axioms C9T00_palette

theorem C9T01_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T01_den) :
    C9T01.Integral p :=
  FibreCert.integral_of_denOk C9T01 C9T01_den p C9T01_den_ok hp

theorem C9T01_palette :
    (∀ d ∈ C9T01.R, C9T01.lf d = poleL 4 0 d ∧ C9T01.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T01.C, C9T01.lf d = poleL 4 0 d ∧ C9T01.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T01_integral
#print axioms C9T01_palette

theorem C9T02_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T02_den) :
    C9T02.Integral p :=
  FibreCert.integral_of_denOk C9T02 C9T02_den p C9T02_den_ok hp

theorem C9T02_palette :
    (∀ d ∈ C9T02.R, C9T02.lf d = poleL 4 1 d ∧ C9T02.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T02.C, C9T02.lf d = poleL 4 1 d ∧ C9T02.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T02_integral
#print axioms C9T02_palette

theorem C9T03_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T03_den) :
    C9T03.Integral p :=
  FibreCert.integral_of_denOk C9T03 C9T03_den p C9T03_den_ok hp

theorem C9T03_palette :
    (∀ d ∈ C9T03.R, C9T03.lf d = poleL 4 1 d ∧ C9T03.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T03.C, C9T03.lf d = poleL 4 1 d ∧ C9T03.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T03_integral
#print axioms C9T03_palette

theorem C9T04_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T04_den) :
    C9T04.Integral p :=
  FibreCert.integral_of_denOk C9T04 C9T04_den p C9T04_den_ok hp

theorem C9T04_palette :
    (∀ d ∈ C9T04.R, C9T04.lf d = poleL 4 1 d ∧ C9T04.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T04.C, C9T04.lf d = poleL 4 1 d ∧ C9T04.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T04_integral
#print axioms C9T04_palette

theorem C9T05_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T05_den) :
    C9T05.Integral p :=
  FibreCert.integral_of_denOk C9T05 C9T05_den p C9T05_den_ok hp

theorem C9T05_palette :
    (∀ d ∈ C9T05.R, C9T05.lf d = poleL 4 1 d ∧ C9T05.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T05.C, C9T05.lf d = poleL 4 1 d ∧ C9T05.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T05_integral
#print axioms C9T05_palette

theorem C9T06_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T06_den) :
    C9T06.Integral p :=
  FibreCert.integral_of_denOk C9T06 C9T06_den p C9T06_den_ok hp

theorem C9T06_palette :
    (∀ d ∈ C9T06.R, C9T06.lf d = poleL 4 1 d ∧ C9T06.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T06.C, C9T06.lf d = poleL 4 1 d ∧ C9T06.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T06_integral
#print axioms C9T06_palette

theorem C9T07_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T07_den) :
    C9T07.Integral p :=
  FibreCert.integral_of_denOk C9T07 C9T07_den p C9T07_den_ok hp

theorem C9T07_palette :
    (∀ d ∈ C9T07.R, C9T07.lf d = poleL 4 0 d ∧ C9T07.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T07.C, C9T07.lf d = poleL 4 0 d ∧ C9T07.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T07_integral
#print axioms C9T07_palette

theorem C9T08_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T08_den) :
    C9T08.Integral p :=
  FibreCert.integral_of_denOk C9T08 C9T08_den p C9T08_den_ok hp

theorem C9T08_palette :
    (∀ d ∈ C9T08.R, C9T08.lf d = poleL 4 0 d ∧ C9T08.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T08.C, C9T08.lf d = poleL 4 0 d ∧ C9T08.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T08_integral
#print axioms C9T08_palette

theorem C9T09_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T09_den) :
    C9T09.Integral p :=
  FibreCert.integral_of_denOk C9T09 C9T09_den p C9T09_den_ok hp

theorem C9T09_palette :
    (∀ d ∈ C9T09.R, C9T09.lf d = poleL 4 0 d ∧ C9T09.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T09.C, C9T09.lf d = poleL 4 0 d ∧ C9T09.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T09_integral
#print axioms C9T09_palette

theorem C9T10_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T10_den) :
    C9T10.Integral p :=
  FibreCert.integral_of_denOk C9T10 C9T10_den p C9T10_den_ok hp

theorem C9T10_palette :
    (∀ d ∈ C9T10.R, C9T10.lf d = poleL 4 1 d ∧ C9T10.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T10.C, C9T10.lf d = poleL 4 1 d ∧ C9T10.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T10_integral
#print axioms C9T10_palette

theorem C9T11_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T11_den) :
    C9T11.Integral p :=
  FibreCert.integral_of_denOk C9T11 C9T11_den p C9T11_den_ok hp

theorem C9T11_palette :
    (∀ d ∈ C9T11.R, C9T11.lf d = poleL 4 1 d ∧ C9T11.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T11.C, C9T11.lf d = poleL 4 1 d ∧ C9T11.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T11_integral
#print axioms C9T11_palette

theorem C9T12_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T12_den) :
    C9T12.Integral p :=
  FibreCert.integral_of_denOk C9T12 C9T12_den p C9T12_den_ok hp

theorem C9T12_palette :
    (∀ d ∈ C9T12.R, C9T12.lf d = poleL 4 1 d ∧ C9T12.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T12.C, C9T12.lf d = poleL 4 1 d ∧ C9T12.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T12_integral
#print axioms C9T12_palette

theorem C9T13_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T13_den) :
    C9T13.Integral p :=
  FibreCert.integral_of_denOk C9T13 C9T13_den p C9T13_den_ok hp

theorem C9T13_palette :
    (∀ d ∈ C9T13.R, C9T13.lf d = poleL 4 0 d ∧ C9T13.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T13.C, C9T13.lf d = poleL 4 0 d ∧ C9T13.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T13_integral
#print axioms C9T13_palette

theorem C9T14_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T14_den) :
    C9T14.Integral p :=
  FibreCert.integral_of_denOk C9T14 C9T14_den p C9T14_den_ok hp

theorem C9T14_palette :
    (∀ d ∈ C9T14.R, C9T14.lf d = poleL 4 0 d ∧ C9T14.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T14.C, C9T14.lf d = poleL 4 0 d ∧ C9T14.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T14_integral
#print axioms C9T14_palette

theorem C9T15_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T15_den) :
    C9T15.Integral p :=
  FibreCert.integral_of_denOk C9T15 C9T15_den p C9T15_den_ok hp

theorem C9T15_palette :
    (∀ d ∈ C9T15.R, C9T15.lf d = poleL 4 0 d ∧ C9T15.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T15.C, C9T15.lf d = poleL 4 0 d ∧ C9T15.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T15_integral
#print axioms C9T15_palette

theorem C9T16_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T16_den) :
    C9T16.Integral p :=
  FibreCert.integral_of_denOk C9T16 C9T16_den p C9T16_den_ok hp

theorem C9T16_palette :
    (∀ d ∈ C9T16.R, C9T16.lf d = poleL 4 1 d ∧ C9T16.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T16.C, C9T16.lf d = poleL 4 1 d ∧ C9T16.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T16_integral
#print axioms C9T16_palette

theorem C9T17_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T17_den) :
    C9T17.Integral p :=
  FibreCert.integral_of_denOk C9T17 C9T17_den p C9T17_den_ok hp

theorem C9T17_palette :
    (∀ d ∈ C9T17.R, C9T17.lf d = poleL 4 1 d ∧ C9T17.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T17.C, C9T17.lf d = poleL 4 1 d ∧ C9T17.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T17_integral
#print axioms C9T17_palette

theorem C9T18_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T18_den) :
    C9T18.Integral p :=
  FibreCert.integral_of_denOk C9T18 C9T18_den p C9T18_den_ok hp

theorem C9T18_palette :
    (∀ d ∈ C9T18.R, C9T18.lf d = poleL 4 1 d ∧ C9T18.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T18.C, C9T18.lf d = poleL 4 1 d ∧ C9T18.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T18_integral
#print axioms C9T18_palette

theorem C9T19_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T19_den) :
    C9T19.Integral p :=
  FibreCert.integral_of_denOk C9T19 C9T19_den p C9T19_den_ok hp

theorem C9T19_palette :
    (∀ d ∈ C9T19.R, C9T19.lf d = poleL 4 0 d ∧ C9T19.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T19.C, C9T19.lf d = poleL 4 0 d ∧ C9T19.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T19_integral
#print axioms C9T19_palette

theorem C9T20_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T20_den) :
    C9T20.Integral p :=
  FibreCert.integral_of_denOk C9T20 C9T20_den p C9T20_den_ok hp

theorem C9T20_palette :
    (∀ d ∈ C9T20.R, C9T20.lf d = poleL 4 0 d ∧ C9T20.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T20.C, C9T20.lf d = poleL 4 0 d ∧ C9T20.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T20_integral
#print axioms C9T20_palette

theorem C9T21_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T21_den) :
    C9T21.Integral p :=
  FibreCert.integral_of_denOk C9T21 C9T21_den p C9T21_den_ok hp

theorem C9T21_palette :
    (∀ d ∈ C9T21.R, C9T21.lf d = poleL 4 0 d ∧ C9T21.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T21.C, C9T21.lf d = poleL 4 0 d ∧ C9T21.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T21_integral
#print axioms C9T21_palette

theorem C9T22_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T22_den) :
    C9T22.Integral p :=
  FibreCert.integral_of_denOk C9T22 C9T22_den p C9T22_den_ok hp

theorem C9T22_palette :
    (∀ d ∈ C9T22.R, C9T22.lf d = poleL 4 1 d ∧ C9T22.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T22.C, C9T22.lf d = poleL 4 1 d ∧ C9T22.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T22_integral
#print axioms C9T22_palette

theorem C9T23_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T23_den) :
    C9T23.Integral p :=
  FibreCert.integral_of_denOk C9T23 C9T23_den p C9T23_den_ok hp

theorem C9T23_palette :
    (∀ d ∈ C9T23.R, C9T23.lf d = poleL 4 0 d ∧ C9T23.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T23.C, C9T23.lf d = poleL 4 0 d ∧ C9T23.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T23_integral
#print axioms C9T23_palette

theorem C9T24_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T24_den) :
    C9T24.Integral p :=
  FibreCert.integral_of_denOk C9T24 C9T24_den p C9T24_den_ok hp

theorem C9T24_palette :
    (∀ d ∈ C9T24.R, C9T24.lf d = poleL 4 1 d ∧ C9T24.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T24.C, C9T24.lf d = poleL 4 1 d ∧ C9T24.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T24_integral
#print axioms C9T24_palette

theorem C9T25_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T25_den) :
    C9T25.Integral p :=
  FibreCert.integral_of_denOk C9T25 C9T25_den p C9T25_den_ok hp

theorem C9T25_palette :
    (∀ d ∈ C9T25.R, C9T25.lf d = poleL 4 1 d ∧ C9T25.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T25.C, C9T25.lf d = poleL 4 1 d ∧ C9T25.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T25_integral
#print axioms C9T25_palette

theorem C9T26_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T26_den) :
    C9T26.Integral p :=
  FibreCert.integral_of_denOk C9T26 C9T26_den p C9T26_den_ok hp

theorem C9T26_palette :
    (∀ d ∈ C9T26.R, C9T26.lf d = poleL 4 0 d ∧ C9T26.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T26.C, C9T26.lf d = poleL 4 0 d ∧ C9T26.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T26_integral
#print axioms C9T26_palette

theorem C9T27_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T27_den) :
    C9T27.Integral p :=
  FibreCert.integral_of_denOk C9T27 C9T27_den p C9T27_den_ok hp

theorem C9T27_palette :
    (∀ d ∈ C9T27.R, C9T27.lf d = poleL 4 0 d ∧ C9T27.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T27.C, C9T27.lf d = poleL 4 0 d ∧ C9T27.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T27_integral
#print axioms C9T27_palette

theorem C9T28_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T28_den) :
    C9T28.Integral p :=
  FibreCert.integral_of_denOk C9T28 C9T28_den p C9T28_den_ok hp

theorem C9T28_palette :
    (∀ d ∈ C9T28.R, C9T28.lf d = poleL 4 1 d ∧ C9T28.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T28.C, C9T28.lf d = poleL 4 1 d ∧ C9T28.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T28_integral
#print axioms C9T28_palette

theorem C9T29_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T29_den) :
    C9T29.Integral p :=
  FibreCert.integral_of_denOk C9T29 C9T29_den p C9T29_den_ok hp

theorem C9T29_palette :
    (∀ d ∈ C9T29.R, C9T29.lf d = poleL 4 0 d ∧ C9T29.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T29.C, C9T29.lf d = poleL 4 0 d ∧ C9T29.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T29_integral
#print axioms C9T29_palette

theorem C9T30_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T30_den) :
    C9T30.Integral p :=
  FibreCert.integral_of_denOk C9T30 C9T30_den p C9T30_den_ok hp

theorem C9T30_palette :
    (∀ d ∈ C9T30.R, C9T30.lf d = poleL 4 1 d ∧ C9T30.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T30.C, C9T30.lf d = poleL 4 1 d ∧ C9T30.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T30_integral
#print axioms C9T30_palette

theorem C9T31_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T31_den) :
    C9T31.Integral p :=
  FibreCert.integral_of_denOk C9T31 C9T31_den p C9T31_den_ok hp

theorem C9T31_palette :
    (∀ d ∈ C9T31.R, C9T31.lf d = poleL 4 1 d ∧ C9T31.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T31.C, C9T31.lf d = poleL 4 1 d ∧ C9T31.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T31_integral
#print axioms C9T31_palette

theorem C9T32_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T32_den) :
    C9T32.Integral p :=
  FibreCert.integral_of_denOk C9T32 C9T32_den p C9T32_den_ok hp

theorem C9T32_palette :
    (∀ d ∈ C9T32.R, C9T32.lf d = poleL 4 1 d ∧ C9T32.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T32.C, C9T32.lf d = poleL 4 1 d ∧ C9T32.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T32_integral
#print axioms C9T32_palette

theorem C9T33_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T33_den) :
    C9T33.Integral p :=
  FibreCert.integral_of_denOk C9T33 C9T33_den p C9T33_den_ok hp

theorem C9T33_palette :
    (∀ d ∈ C9T33.R, C9T33.lf d = poleL 4 0 d ∧ C9T33.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T33.C, C9T33.lf d = poleL 4 0 d ∧ C9T33.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T33_integral
#print axioms C9T33_palette

theorem C9T34_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T34_den) :
    C9T34.Integral p :=
  FibreCert.integral_of_denOk C9T34 C9T34_den p C9T34_den_ok hp

theorem C9T34_palette :
    (∀ d ∈ C9T34.R, C9T34.lf d = poleL 4 0 d ∧ C9T34.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T34.C, C9T34.lf d = poleL 4 0 d ∧ C9T34.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T34_integral
#print axioms C9T34_palette

theorem C9T35_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T35_den) :
    C9T35.Integral p :=
  FibreCert.integral_of_denOk C9T35 C9T35_den p C9T35_den_ok hp

theorem C9T35_palette :
    (∀ d ∈ C9T35.R, C9T35.lf d = poleL 4 0 d ∧ C9T35.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T35.C, C9T35.lf d = poleL 4 0 d ∧ C9T35.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T35_integral
#print axioms C9T35_palette

theorem C9T36_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T36_den) :
    C9T36.Integral p :=
  FibreCert.integral_of_denOk C9T36 C9T36_den p C9T36_den_ok hp

theorem C9T36_palette :
    (∀ d ∈ C9T36.R, C9T36.lf d = poleL 4 1 d ∧ C9T36.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T36.C, C9T36.lf d = poleL 4 1 d ∧ C9T36.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T36_integral
#print axioms C9T36_palette

theorem C9T37_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T37_den) :
    C9T37.Integral p :=
  FibreCert.integral_of_denOk C9T37 C9T37_den p C9T37_den_ok hp

theorem C9T37_palette :
    (∀ d ∈ C9T37.R, C9T37.lf d = poleL 4 1 d ∧ C9T37.ee d = poleE 4 1 d) ∧
    (∀ d ∈ C9T37.C, C9T37.lf d = poleL 4 1 d ∧ C9T37.ee d = poleE 4 1 d) := by
  constructor <;> decide +kernel

#print axioms C9T37_integral
#print axioms C9T37_palette

theorem C9T38_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T38_den) :
    C9T38.Integral p :=
  FibreCert.integral_of_denOk C9T38 C9T38_den p C9T38_den_ok hp

theorem C9T38_palette :
    (∀ d ∈ C9T38.R, C9T38.lf d = poleL 4 0 d ∧ C9T38.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T38.C, C9T38.lf d = poleL 4 0 d ∧ C9T38.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T38_integral
#print axioms C9T38_palette

theorem C9T39_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C9T39_den) :
    C9T39.Integral p :=
  FibreCert.integral_of_denOk C9T39 C9T39_den p C9T39_den_ok hp

theorem C9T39_palette :
    (∀ d ∈ C9T39.R, C9T39.lf d = poleL 4 0 d ∧ C9T39.ee d = poleE 4 0 d) ∧
    (∀ d ∈ C9T39.C, C9T39.lf d = poleL 4 0 d ∧ C9T39.ee d = poleE 4 0 d) := by
  constructor <;> decide +kernel

#print axioms C9T39_integral
#print axioms C9T39_palette

end CatalanCore.Uniform.Bank.Sevenths.RankData
