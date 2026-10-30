import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C3T26
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T26_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T26_den) :
    C3T26.Integral p :=
  RankTools.integral_of_denOk C3T26 C3T26_den p C3T26_den_ok hp

/-- Digit palette at root 3, cyclic pole bit 0, on every coordinate. -/
theorem C3T26_palette :
    (∀ d ∈ C3T26.R, C3T26.lf d = poleL 3 0 d ∧ C3T26.ee d = poleE 3 0 d) ∧
    (∀ d ∈ C3T26.C, C3T26.lf d = poleL 3 0 d ∧ C3T26.ee d = poleE 3 0 d) := by
  constructor <;> decide +kernel
theorem C3T26_loads_nonzero :
    (∀ d ∈ C3T26.kr, C3T26.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C3T26.kc, C3T26.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C3T26_load_orthogonal : ∀ r ∈ C3T26.kr, ∀ c ∈ C3T26.kc,
    (C3T26.rload r).1 * (C3T26.cload c).2 -
      (C3T26.rload r).2 * (C3T26.cload c).1 = 0 := by decide +kernel
#print axioms C3T26_integral
#print axioms C3T26_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
