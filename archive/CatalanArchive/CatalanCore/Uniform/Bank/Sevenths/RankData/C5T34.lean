import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 0637f12c6ac0f98341a1ad77fdc9a775cabe7bf1257c95491021cf3a7f957604, root class 5. -/
def C5T34 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => 0 | 1 => (-4 / 3) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-40 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C5T34_ok : C5T34.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T34_den : ℕ := 1
theorem C5T34_den_ok :
    (∀ d ∈ C5T34.R, ∀ e ∈ C5T34.R, (C5T34.Lq d e).den ∣ C5T34_den ∧ (C5T34.Lq' d e).den ∣ C5T34_den) ∧
    (∀ d ∈ C5T34.C, ∀ e ∈ C5T34.C, (C5T34.Pq d e).den ∣ C5T34_den ∧ (C5T34.Pq' d e).den ∣ C5T34_den) := by
  constructor <;> decide +kernel
theorem C5T34_rload_1 : C5T34.rload 1 = (1, 0) := by decide +kernel
#print axioms C5T34_ok
#print axioms C5T34_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
