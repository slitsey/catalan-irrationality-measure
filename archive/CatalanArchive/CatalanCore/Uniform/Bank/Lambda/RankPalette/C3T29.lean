import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C3T29
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T29_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T29_den) :
    C3T29.Integral p :=
  RankTools.integral_of_denOk C3T29 C3T29_den p C3T29_den_ok hp

/-- Digit palette at root 3, cyclic pole bit 0, on every coordinate. -/
theorem C3T29_palette :
    (∀ d ∈ C3T29.R, C3T29.lf d = poleL 3 0 d ∧ C3T29.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C3T29.C, C3T29.lf d = poleL 3 0 d ∧ C3T29.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel
theorem C3T29_loads_nonzero :
    (∀ d ∈ C3T29.kr, C3T29.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C3T29.kc, C3T29.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C3T29_load_orthogonal : ∀ r ∈ C3T29.kr, ∀ c ∈ C3T29.kc,
    (C3T29.rload r).1 * (C3T29.cload c).2 -
      (C3T29.rload r).2 * (C3T29.cload c).1 = 0 := by decide +kernel
#print axioms C3T29_integral
#print axioms C3T29_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
