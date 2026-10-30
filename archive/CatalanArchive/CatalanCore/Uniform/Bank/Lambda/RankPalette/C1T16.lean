import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C1T16
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C1T16_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T16_den) :
    C1T16.Integral p :=
  RankTools.integral_of_denOk C1T16 C1T16_den p C1T16_den_ok hp

/-- Digit palette at root 1, cyclic pole bit 0, on every coordinate. -/
theorem C1T16_palette :
    (∀ d ∈ C1T16.R, C1T16.lf d = poleL 1 0 d ∧ C1T16.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T16.C, C1T16.lf d = poleL 1 0 d ∧ C1T16.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel
theorem C1T16_loads_nonzero :
    (∀ d ∈ C1T16.kr, C1T16.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C1T16.kc, C1T16.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C1T16_load_orthogonal : ∀ r ∈ C1T16.kr, ∀ c ∈ C1T16.kc,
    (C1T16.rload r).1 * (C1T16.cload c).2 -
      (C1T16.rload r).2 * (C1T16.cload c).1 = 0 := by decide +kernel
#print axioms C1T16_integral
#print axioms C1T16_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
