import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 2aa6f2d362de8b86a8423440b99386e1aa393898dc78ec77ea7076377635b238, root class 9. -/
def C9T22 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7 / 4) | 1 => (-61 / 44) | 2 => (-505 / 396) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | 1 => (-4777 / 1936) | 2 => (-371449 / 156816) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T22_ok : C9T22.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T22_den : ℕ := 1
theorem C9T22_den_ok :
    (∀ d ∈ C9T22.R, ∀ e ∈ C9T22.R, (C9T22.Lq d e).den ∣ C9T22_den ∧ (C9T22.Lq' d e).den ∣ C9T22_den) ∧
    (∀ d ∈ C9T22.C, ∀ e ∈ C9T22.C, (C9T22.Pq d e).den ∣ C9T22_den ∧ (C9T22.Pq' d e).den ∣ C9T22_den) := by
  constructor <;> decide +kernel
#print axioms C9T22_ok
#print axioms C9T22_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
