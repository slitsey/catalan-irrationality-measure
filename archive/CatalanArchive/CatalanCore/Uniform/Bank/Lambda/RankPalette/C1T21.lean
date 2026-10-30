import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C1T21
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C1T21_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T21_den) :
    C1T21.Integral p :=
  RankTools.integral_of_denOk C1T21 C1T21_den p C1T21_den_ok hp

/-- Digit palette at root 1, cyclic pole bit 0, on every coordinate. -/
theorem C1T21_palette :
    (∀ d ∈ C1T21.R, C1T21.lf d = poleL 1 0 d ∧ C1T21.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T21.C, C1T21.lf d = poleL 1 0 d ∧ C1T21.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel
theorem C1T21_loads_nonzero :
    (∀ d ∈ C1T21.kr, C1T21.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C1T21.kc, C1T21.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C1T21_load_orthogonal : ∀ r ∈ C1T21.kr, ∀ c ∈ C1T21.kc,
    (C1T21.rload r).1 * (C1T21.cload c).2 -
      (C1T21.rload r).2 * (C1T21.cload c).1 = 0 := by decide +kernel
#print axioms C1T21_integral
#print axioms C1T21_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
