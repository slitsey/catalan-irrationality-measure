import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C3T07
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T07_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T07_den) :
    C3T07.Integral p :=
  RankTools.integral_of_denOk C3T07 C3T07_den p C3T07_den_ok hp

/-- Digit palette at root 3, cyclic pole bit 0, on every coordinate. -/
theorem C3T07_palette :
    (∀ d ∈ C3T07.R, C3T07.lf d = poleL 3 0 d ∧ C3T07.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C3T07.C, C3T07.lf d = poleL 3 0 d ∧ C3T07.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel
theorem C3T07_loads_nonzero :
    (∀ d ∈ C3T07.kr, C3T07.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C3T07.kc, C3T07.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C3T07_load_orthogonal : ∀ r ∈ C3T07.kr, ∀ c ∈ C3T07.kc,
    (C3T07.rload r).1 * (C3T07.cload c).2 -
      (C3T07.rload r).2 * (C3T07.cload c).1 = 0 := by decide +kernel
#print axioms C3T07_integral
#print axioms C3T07_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
