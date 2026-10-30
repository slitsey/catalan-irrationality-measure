import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type facbb4e334ba55fc901a85d92e5c7540fba967aa7d6c5559a35aacaebc2f7c9f, root class 5. -/
def C5T29 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-4 / 3) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-40 / 9) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C5T29_ok : C5T29.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T29_den : ℕ := 1
theorem C5T29_den_ok :
    (∀ d ∈ C5T29.R, ∀ e ∈ C5T29.R, (C5T29.Lq d e).den ∣ C5T29_den ∧ (C5T29.Lq' d e).den ∣ C5T29_den) ∧
    (∀ d ∈ C5T29.C, ∀ e ∈ C5T29.C, (C5T29.Pq d e).den ∣ C5T29_den ∧ (C5T29.Pq' d e).den ∣ C5T29_den) := by
  constructor <;> decide +kernel
#print axioms C5T29_ok
#print axioms C5T29_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
