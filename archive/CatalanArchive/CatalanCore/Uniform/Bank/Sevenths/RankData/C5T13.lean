import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type b4d0ccfc8f32d62f09219f093c214b21603f35b69bca1fa36ad51d58de83ed5f, root class 5. -/
def C5T13 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-4 / 3) | 2 => (-23 / 15) | 3 => (-137 / 85) | 4 => (-3373 / 2040) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-40 / 9) | 2 => (-1054 / 225) | 3 => (-102802 / 21675) | 4 => (-19831909 / 4161600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C5T13_ok : C5T13.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T13_den : ℕ := 1
theorem C5T13_den_ok :
    (∀ d ∈ C5T13.R, ∀ e ∈ C5T13.R, (C5T13.Lq d e).den ∣ C5T13_den ∧ (C5T13.Lq' d e).den ∣ C5T13_den) ∧
    (∀ d ∈ C5T13.C, ∀ e ∈ C5T13.C, (C5T13.Pq d e).den ∣ C5T13_den ∧ (C5T13.Pq' d e).den ∣ C5T13_den) := by
  constructor <;> decide +kernel
#print axioms C5T13_ok
#print axioms C5T13_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
