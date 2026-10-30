import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type bc03ead55631cd7a4e5f282ba6d2d3e2ff22020bee149e6c5f2d759d19931568, root class 5. -/
def C5T25 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-4 / 3) | 2 => (-23 / 15) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-40 / 9) | 2 => (-1054 / 225) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C5T25_ok : C5T25.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T25_den : ℕ := 1
theorem C5T25_den_ok :
    (∀ d ∈ C5T25.R, ∀ e ∈ C5T25.R, (C5T25.Lq d e).den ∣ C5T25_den ∧ (C5T25.Lq' d e).den ∣ C5T25_den) ∧
    (∀ d ∈ C5T25.C, ∀ e ∈ C5T25.C, (C5T25.Pq d e).den ∣ C5T25_den ∧ (C5T25.Pq' d e).den ∣ C5T25_den) := by
  constructor <;> decide +kernel
#print axioms C5T25_ok
#print axioms C5T25_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
