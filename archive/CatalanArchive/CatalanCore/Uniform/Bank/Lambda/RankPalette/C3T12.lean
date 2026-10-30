import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C3T12
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T12_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T12_den) :
    C3T12.Integral p :=
  RankTools.integral_of_denOk C3T12 C3T12_den p C3T12_den_ok hp

/-- Digit palette at root 3, cyclic pole bit 1, on every coordinate. -/
theorem C3T12_palette :
    (∀ d ∈ C3T12.R, C3T12.lf d = poleL 3 1 d ∧ C3T12.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C3T12.C, C3T12.lf d = poleL 3 1 d ∧ C3T12.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel
theorem C3T12_loads_nonzero :
    (∀ d ∈ C3T12.kr, C3T12.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C3T12.kc, C3T12.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C3T12_load_orthogonal : ∀ r ∈ C3T12.kr, ∀ c ∈ C3T12.kc,
    (C3T12.rload r).1 * (C3T12.cload c).2 -
      (C3T12.rload r).2 * (C3T12.cload c).1 = 0 := by decide +kernel
#print axioms C3T12_integral
#print axioms C3T12_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
