import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type ed6f5721d87f6f6a27bf99d1411b012b6f979aa4c6487bf501eefc48ec31fcdb, root class 9. -/
def C9T29 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T29_ok : C9T29.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T29_den : ℕ := 1
theorem C9T29_den_ok :
    (∀ d ∈ C9T29.R, ∀ e ∈ C9T29.R, (C9T29.Lq d e).den ∣ C9T29_den ∧ (C9T29.Lq' d e).den ∣ C9T29_den) ∧
    (∀ d ∈ C9T29.C, ∀ e ∈ C9T29.C, (C9T29.Pq d e).den ∣ C9T29_den ∧ (C9T29.Pq' d e).den ∣ C9T29_den) := by
  constructor <;> decide +kernel
#print axioms C9T29_ok
#print axioms C9T29_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
