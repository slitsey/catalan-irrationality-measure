import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 990ab27e12a8c95dc8f99b5e5b0cea96be63b7c8588c35a0630a05d56bc68ecd, root class 5. -/
def C5T26 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7 / 3) | 1 => (-61 / 30) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | 1 => (-4441 / 900) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C5T26_ok : C5T26.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T26_den : ℕ := 1
theorem C5T26_den_ok :
    (∀ d ∈ C5T26.R, ∀ e ∈ C5T26.R, (C5T26.Lq d e).den ∣ C5T26_den ∧ (C5T26.Lq' d e).den ∣ C5T26_den) ∧
    (∀ d ∈ C5T26.C, ∀ e ∈ C5T26.C, (C5T26.Pq d e).den ∣ C5T26_den ∧ (C5T26.Pq' d e).den ∣ C5T26_den) := by
  constructor <;> decide +kernel
#print axioms C5T26_ok
#print axioms C5T26_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
