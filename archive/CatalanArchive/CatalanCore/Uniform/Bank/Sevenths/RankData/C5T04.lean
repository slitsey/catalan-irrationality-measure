import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 3cf8e64244539d5da8b0656ccd18798d55ce285489279dc3b129e4dfbd7b48ed, root class 5. -/
def C5T04 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => (-7 / 3) | 1 => (-61 / 30) | 2 => (-496 / 255) | 3 => (-3883 / 2040) | 4 => (-118843 / 63240) | 5 => (-447809 / 240312) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | 1 => (-4441 / 900) | 2 => (-315631 / 65025) | 3 => (-20092009 / 4161600) | 4 => (-19262382949 / 3999297600) | 5 => (-1388992356569 / 288749286720) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C5T04_ok : C5T04.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T04_den : ℕ := 1
theorem C5T04_den_ok :
    (∀ d ∈ C5T04.R, ∀ e ∈ C5T04.R, (C5T04.Lq d e).den ∣ C5T04_den ∧ (C5T04.Lq' d e).den ∣ C5T04_den) ∧
    (∀ d ∈ C5T04.C, ∀ e ∈ C5T04.C, (C5T04.Pq d e).den ∣ C5T04_den ∧ (C5T04.Pq' d e).den ∣ C5T04_den) := by
  constructor <;> decide +kernel
#print axioms C5T04_ok
#print axioms C5T04_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
