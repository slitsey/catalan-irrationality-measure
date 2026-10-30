import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C3T09
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T09_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T09_den) :
    C3T09.Integral p :=
  RankTools.integral_of_denOk C3T09 C3T09_den p C3T09_den_ok hp

/-- Digit palette at root 3, cyclic pole bit 0, on every coordinate. -/
theorem C3T09_palette :
    (∀ d ∈ C3T09.R, C3T09.lf d = poleL 3 0 d ∧ C3T09.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C3T09.C, C3T09.lf d = poleL 3 0 d ∧ C3T09.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel
theorem C3T09_loads_nonzero :
    (∀ d ∈ C3T09.kr, C3T09.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C3T09.kc, C3T09.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C3T09_load_orthogonal : ∀ r ∈ C3T09.kr, ∀ c ∈ C3T09.kc,
    (C3T09.rload r).1 * (C3T09.cload c).2 -
      (C3T09.rload r).2 * (C3T09.cload c).1 = 0 := by decide +kernel
#print axioms C3T09_integral
#print axioms C3T09_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
