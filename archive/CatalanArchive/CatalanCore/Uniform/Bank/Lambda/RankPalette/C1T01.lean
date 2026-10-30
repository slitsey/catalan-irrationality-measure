import CatalanCore.Uniform.Bank.Lambda.PolePalette
import CatalanCore.Uniform.Bank.Lambda.RankTools
import CatalanCore.Uniform.Bank.Lambda.RankData.C1T01
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore.Uniform.Content.RankProducer

theorem C1T01_integral (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ C1T01_den) :
    C1T01.Integral p :=
  RankTools.integral_of_denOk C1T01 C1T01_den p C1T01_den_ok hp

/-- Digit palette at root 1, cyclic pole bit 0, on every coordinate. -/
theorem C1T01_palette :
    (∀ d ∈ C1T01.R, C1T01.lf d = poleL 1 0 d ∧ C1T01.ee d = poleE 1 0 d) ∧
    (∀ d ∈ C1T01.C, C1T01.lf d = poleL 1 0 d ∧ C1T01.ee d = poleE 1 0 d) := by
  constructor <;> decide +kernel
theorem C1T01_loads_nonzero :
    (∀ d ∈ C1T01.kr, C1T01.rload d ≠ (0, 0)) ∧
    (∀ d ∈ C1T01.kc, C1T01.cload d ≠ (0, 0)) := by
  constructor <;> decide +kernel

theorem C1T01_load_orthogonal : ∀ r ∈ C1T01.kr, ∀ c ∈ C1T01.kc,
    (C1T01.rload r).1 * (C1T01.cload c).2 -
      (C1T01.rload r).2 * (C1T01.cload c).1 = 0 := by decide +kernel
#print axioms C1T01_integral
#print axioms C1T01_palette
end CatalanCore.Uniform.Bank.Lambda.RankData
