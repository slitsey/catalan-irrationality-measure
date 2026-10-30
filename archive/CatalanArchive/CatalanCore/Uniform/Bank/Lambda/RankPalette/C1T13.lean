import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C1T13
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C1T13_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T13_den) :
    C1T13.Integral p :=
  RankTools.integral_of_denOk C1T13 C1T13_den p C1T13_den_ok hp

/-- Digit palette at root 1, cyclic pole bit 0, on every coordinate. -/
theorem C1T13_palette :
    (∀ d ∈ C1T13.R, C1T13.lf d = poleL 1 0 d ∧ C1T13.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T13.C, C1T13.lf d = poleL 1 0 d ∧ C1T13.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel
theorem C1T13_loads_nonzero :
    (∀ d ∈ C1T13.kr, C1T13.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C1T13.kc, C1T13.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C1T13_load_orthogonal : ∀ r ∈ C1T13.kr, ∀ c ∈ C1T13.kc,
    (C1T13.rload r).1 * (C1T13.cload c).2 -
      (C1T13.rload r).2 * (C1T13.cload c).1 = 0 := by decide +kernel
#print axioms C1T13_integral
#print axioms C1T13_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
