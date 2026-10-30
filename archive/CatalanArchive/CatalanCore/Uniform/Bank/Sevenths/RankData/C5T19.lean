import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 578bb52a1addd6ec1ee2b4e3d3ba49aafa8c76904e3f422bc89225b72cc97082, root class 5. -/
def C5T19 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-4 / 3) | 2 => (-23 / 15) | 3 => (-137 / 85) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-40 / 9) | 2 => (-1054 / 225) | 3 => (-102802 / 21675) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C5T19_ok : C5T19.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T19_den : ℕ := 1
theorem C5T19_den_ok :
    (∀ d ∈ C5T19.R, ∀ e ∈ C5T19.R, (C5T19.Lq d e).den ∣ C5T19_den ∧ (C5T19.Lq' d e).den ∣ C5T19_den) ∧
    (∀ d ∈ C5T19.C, ∀ e ∈ C5T19.C, (C5T19.Pq d e).den ∣ C5T19_den ∧ (C5T19.Pq' d e).den ∣ C5T19_den) := by
  constructor <;> decide +kernel
#print axioms C5T19_ok
#print axioms C5T19_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
