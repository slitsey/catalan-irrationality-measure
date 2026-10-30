import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 5cad97bae020e2903aa23267d47d8254c78e52013c5db56f73fb0d31d4f329b9, root class 9. -/
def C9T13 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | 2 => (-39 / 44) | 3 => (-373 / 396) | 4 => (-4811 / 4950) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | 2 => (-4293 / 1936) | 3 => (-354025 / 156816) | 4 => (-13926499 / 6125625) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T13_ok : C9T13.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T13_den : ℕ := 1
theorem C9T13_den_ok :
    (∀ d ∈ C9T13.R, ∀ e ∈ C9T13.R, (C9T13.Lq d e).den ∣ C9T13_den ∧ (C9T13.Lq' d e).den ∣ C9T13_den) ∧
    (∀ d ∈ C9T13.C, ∀ e ∈ C9T13.C, (C9T13.Pq d e).den ∣ C9T13_den ∧ (C9T13.Pq' d e).den ∣ C9T13_den) := by
  constructor <;> decide +kernel
#print axioms C9T13_ok
#print axioms C9T13_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
