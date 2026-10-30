import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type dbb0a583d34dda238db7106363f860a9368bafece06da9f332e5bd311cdbffd3, root class 5. -/
def C5T16 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-7 / 3) | 1 => (-61 / 30) | 2 => (-496 / 255) | 3 => (-3883 / 2040) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | 1 => (-4441 / 900) | 2 => (-315631 / 65025) | 3 => (-20092009 / 4161600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C5T16_ok : C5T16.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T16_den : ℕ := 1
theorem C5T16_den_ok :
    (∀ d ∈ C5T16.R, ∀ e ∈ C5T16.R, (C5T16.Lq d e).den ∣ C5T16_den ∧ (C5T16.Lq' d e).den ∣ C5T16_den) ∧
    (∀ d ∈ C5T16.C, ∀ e ∈ C5T16.C, (C5T16.Pq d e).den ∣ C5T16_den ∧ (C5T16.Pq' d e).den ∣ C5T16_den) := by
  constructor <;> decide +kernel
#print axioms C5T16_ok
#print axioms C5T16_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
