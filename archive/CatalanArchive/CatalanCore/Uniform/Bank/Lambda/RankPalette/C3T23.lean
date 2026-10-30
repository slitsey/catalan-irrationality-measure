import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C3T23
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T23_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T23_den) :
    C3T23.Integral p :=
  RankTools.integral_of_denOk C3T23 C3T23_den p C3T23_den_ok hp

/-- Digit palette at root 3, cyclic pole bit 0, on every coordinate. -/
theorem C3T23_palette :
    (∀ d ∈ C3T23.R, C3T23.lf d = poleL 3 0 d ∧ C3T23.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C3T23.C, C3T23.lf d = poleL 3 0 d ∧ C3T23.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel
theorem C3T23_loads_nonzero :
    (∀ d ∈ C3T23.kr, C3T23.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C3T23.kc, C3T23.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C3T23_load_orthogonal : ∀ r ∈ C3T23.kr, ∀ c ∈ C3T23.kc,
    (C3T23.rload r).1 * (C3T23.cload c).2 -
      (C3T23.rload r).2 * (C3T23.cload c).1 = 0 := by decide +kernel
#print axioms C3T23_integral
#print axioms C3T23_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
