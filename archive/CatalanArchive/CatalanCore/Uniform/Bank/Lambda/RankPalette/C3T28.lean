import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C3T28
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T28_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T28_den) :
    C3T28.Integral p :=
  RankTools.integral_of_denOk C3T28 C3T28_den p C3T28_den_ok hp

/-- Digit palette at root 3, cyclic pole bit 1, on every coordinate. -/
theorem C3T28_palette :
    (∀ d ∈ C3T28.R, C3T28.lf d = poleL 3 1 d ∧ C3T28.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C3T28.C, C3T28.lf d = poleL 3 1 d ∧ C3T28.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel
theorem C3T28_loads_nonzero :
    (∀ d ∈ C3T28.kr, C3T28.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C3T28.kc, C3T28.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C3T28_load_orthogonal : ∀ r ∈ C3T28.kr, ∀ c ∈ C3T28.kc,
    (C3T28.rload r).1 * (C3T28.cload c).2 -
      (C3T28.rload r).2 * (C3T28.cload c).1 = 0 := by decide +kernel
#print axioms C3T28_integral
#print axioms C3T28_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
