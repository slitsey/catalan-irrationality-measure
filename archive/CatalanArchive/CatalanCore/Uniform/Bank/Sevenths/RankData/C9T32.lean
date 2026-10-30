import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 4ff84b5a179ea2560bb25b6802e446ca1b9b42b8aedfd34beb3204be9ca46bbe, root class 9. -/
def C9T32 : FibreCert where
  R := {0}
  C := {0}
  lf := fun d => match d with | 0 => (-7 / 4) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T32_ok : C9T32.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T32_den : ℕ := 1
theorem C9T32_den_ok :
    (∀ d ∈ C9T32.R, ∀ e ∈ C9T32.R, (C9T32.Lq d e).den ∣ C9T32_den ∧ (C9T32.Lq' d e).den ∣ C9T32_den) ∧
    (∀ d ∈ C9T32.C, ∀ e ∈ C9T32.C, (C9T32.Pq d e).den ∣ C9T32_den ∧ (C9T32.Pq' d e).den ∣ C9T32_den) := by
  constructor <;> decide +kernel
#print axioms C9T32_ok
#print axioms C9T32_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
