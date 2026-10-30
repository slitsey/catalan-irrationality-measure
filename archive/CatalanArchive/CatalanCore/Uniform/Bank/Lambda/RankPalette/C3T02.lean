import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C3T02
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T02_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T02_den) :
    C3T02.Integral p :=
  RankTools.integral_of_denOk C3T02 C3T02_den p C3T02_den_ok hp

/-- Digit palette at root 3, cyclic pole bit 1, on every coordinate. -/
theorem C3T02_palette :
    (∀ d ∈ C3T02.R, C3T02.lf d = poleL 3 1 d ∧ C3T02.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C3T02.C, C3T02.lf d = poleL 3 1 d ∧ C3T02.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel
theorem C3T02_loads_nonzero :
    (∀ d ∈ C3T02.kr, C3T02.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C3T02.kc, C3T02.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C3T02_load_orthogonal : ∀ r ∈ C3T02.kr, ∀ c ∈ C3T02.kc,
    (C3T02.rload r).1 * (C3T02.cload c).2 -
      (C3T02.rload r).2 * (C3T02.cload c).1 = 0 := by decide +kernel
#print axioms C3T02_integral
#print axioms C3T02_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
