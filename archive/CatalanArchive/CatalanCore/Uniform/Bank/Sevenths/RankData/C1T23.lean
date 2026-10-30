import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 7ac171d7028026429123d0f017eb6d91b16213ffc0821fc19fea60b34183a158, root class 1. -/
def C1T23 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7) | 1 => (-55 / 8) | 2 => (-821 / 120) | _ => 0
  ee := fun d => match d with | 0 => (-49) | 1 => (-3121 / 64) | 2 => (-701761 / 14400) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (-3949 / 2446848) | 2, 1 => (-1039 / 1529280) | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 0 => (3949 / 2446848) | 2, 1 => (1039 / 1529280) | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := {2}
  kc := ∅

theorem C1T23_ok : C1T23.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T23_den : ℕ := 12234240
theorem C1T23_den_ok :
    (∀ d ∈ C1T23.R, ∀ e ∈ C1T23.R, (C1T23.Lq d e).den ∣ C1T23_den ∧ (C1T23.Lq' d e).den ∣ C1T23_den) ∧
    (∀ d ∈ C1T23.C, ∀ e ∈ C1T23.C, (C1T23.Pq d e).den ∣ C1T23_den ∧ (C1T23.Pq' d e).den ∣ C1T23_den) := by
  constructor <;> decide +kernel
theorem C1T23_rload_2 : C1T23.rload 2 = ((12206183 / 12234240), (-869867 / 127440)) := by decide +kernel
#print axioms C1T23_ok
#print axioms C1T23_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
