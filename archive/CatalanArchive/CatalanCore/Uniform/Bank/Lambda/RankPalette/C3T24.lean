import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C3T24
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C3T24_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C3T24_den) :
    C3T24.Integral p :=
  RankTools.integral_of_denOk C3T24 C3T24_den p C3T24_den_ok hp

/-- Digit palette at root 3, cyclic pole bit 1, on every coordinate. -/
theorem C3T24_palette :
    (∀ d ∈ C3T24.R, C3T24.lf d = poleL 3 1 d ∧ C3T24.ee d = poleE 3 1 d) ∧
    (∀ d ∈ C3T24.C, C3T24.lf d = poleL 3 1 d ∧ C3T24.ee d = poleE 3 1 d) := by
  constructor <;> decide +kernel
theorem C3T24_loads_nonzero :
    (∀ d ∈ C3T24.kr, C3T24.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C3T24.kc, C3T24.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C3T24_load_orthogonal : ∀ r ∈ C3T24.kr, ∀ c ∈ C3T24.kc,
    (C3T24.rload r).1 * (C3T24.cload c).2 -
      (C3T24.rload r).2 * (C3T24.cload c).1 = 0 := by decide +kernel
#print axioms C3T24_integral
#print axioms C3T24_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
