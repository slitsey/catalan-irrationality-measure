import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type dbe9847709738b09d5f7708f4ab406d6ebd4cd02d04eafb1d04365c8be350c7d, root class 5. -/
def C5T22 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-7 / 3) | 1 => (-61 / 30) | 2 => (-496 / 255) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | 1 => (-4441 / 900) | 2 => (-315631 / 65025) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C5T22_ok : C5T22.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T22_den : ℕ := 1
theorem C5T22_den_ok :
    (∀ d ∈ C5T22.R, ∀ e ∈ C5T22.R, (C5T22.Lq d e).den ∣ C5T22_den ∧ (C5T22.Lq' d e).den ∣ C5T22_den) ∧
    (∀ d ∈ C5T22.C, ∀ e ∈ C5T22.C, (C5T22.Pq d e).den ∣ C5T22_den ∧ (C5T22.Pq' d e).den ∣ C5T22_den) := by
  constructor <;> decide +kernel
#print axioms C5T22_ok
#print axioms C5T22_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
