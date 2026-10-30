import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C3T20
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T20_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T20_den) :
    C3T20.Integral p :=
  RankTools.integral_of_denOk C3T20 C3T20_den p C3T20_den_ok hp

/-- Digit palette at root 3, cyclic pole bit 0, on every coordinate. -/
theorem C3T20_palette :
    (∀ d ∈ C3T20.R, C3T20.lf d = poleL 3 0 d ∧ C3T20.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C3T20.C, C3T20.lf d = poleL 3 0 d ∧ C3T20.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel
theorem C3T20_loads_nonzero :
    (∀ d ∈ C3T20.kr, C3T20.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C3T20.kc, C3T20.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C3T20_load_orthogonal : ∀ r ∈ C3T20.kr, ∀ c ∈ C3T20.kc,
    (C3T20.rload r).1 * (C3T20.cload c).2 -
      (C3T20.rload r).2 * (C3T20.cload c).1 = 0 := by decide +kernel
#print axioms C3T20_integral
#print axioms C3T20_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
