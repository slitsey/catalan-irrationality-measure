import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C1T20
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C1T20_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T20_den) :
    C1T20.Integral p :=
  RankTools.integral_of_denOk C1T20 C1T20_den p C1T20_den_ok hp

/-- Digit palette at root 1, cyclic pole bit 1, on every coordinate. -/
theorem C1T20_palette :
    (∀ d ∈ C1T20.R, C1T20.lf d = poleL 1 1 d ∧ C1T20.ee d = poleE 1 1 d) ∧
    (∀ d ∈ C1T20.C, C1T20.lf d = poleL 1 1 d ∧ C1T20.ee d = poleE 1 1 d) := by
  constructor <;> decide +kernel
theorem C1T20_loads_nonzero :
    (∀ d ∈ C1T20.kr, C1T20.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C1T20.kc, C1T20.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C1T20_load_orthogonal : ∀ r ∈ C1T20.kr, ∀ c ∈ C1T20.kc,
    (C1T20.rload r).1 * (C1T20.cload c).2 -
      (C1T20.rload r).2 * (C1T20.cload c).1 = 0 := by decide +kernel
#print axioms C1T20_integral
#print axioms C1T20_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
