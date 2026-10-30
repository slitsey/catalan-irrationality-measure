import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 1966d77d8fdc2eabc7157814a7577b880c1e9676c28eab880432d1c6ed4c19d7, root class 1. -/
def C1T22 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-6) | 2 => (-51 / 8) | 3 => (-781 / 120) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-48) | 2 => (-3105 / 64) | 3 => (-233387 / 4800) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (-10540603 / 4605120) | 3, 1 => (-2597161 / 9210240) | 3, 2 => (-1597 / 10660) | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 0 => (10540603 / 4605120) | 3, 1 => (2597161 / 9210240) | 3, 2 => (1597 / 10660) | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := {3}
  kc := ∅

theorem C1T22_ok : C1T22.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T22_den : ℕ := 9210240
theorem C1T22_den_ok :
    (∀ d ∈ C1T22.R, ∀ e ∈ C1T22.R, (C1T22.Lq d e).den ∣ C1T22_den ∧ (C1T22.Lq' d e).den ∣ C1T22_den) ∧
    (∀ d ∈ C1T22.C, ∀ e ∈ C1T22.C, (C1T22.Pq d e).den ∣ C1T22_den ∧ (C1T22.Pq' d e).den ∣ C1T22_den) := by
  constructor <;> decide +kernel
theorem C1T22_rload_3 : C1T22.rload 3 = ((-25769 / 14976), (-1185469 / 307008)) := by decide +kernel
#print axioms C1T22_ok
#print axioms C1T22_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
