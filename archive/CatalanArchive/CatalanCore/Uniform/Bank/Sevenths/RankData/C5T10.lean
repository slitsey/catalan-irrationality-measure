import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type b64abcd892b4c72da899bd7b3df97d2bb95c1314dec1b56c18e43b878e14ac93, root class 5. -/
def C5T10 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-7 / 3) | 1 => (-61 / 30) | 2 => (-496 / 255) | 3 => (-3883 / 2040) | 4 => (-118843 / 63240) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 9) | 1 => (-4441 / 900) | 2 => (-315631 / 65025) | 3 => (-20092009 / 4161600) | 4 => (-19262382949 / 3999297600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C5T10_ok : C5T10.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C5T10_den : ℕ := 1
theorem C5T10_den_ok :
    (∀ d ∈ C5T10.R, ∀ e ∈ C5T10.R, (C5T10.Lq d e).den ∣ C5T10_den ∧ (C5T10.Lq' d e).den ∣ C5T10_den) ∧
    (∀ d ∈ C5T10.C, ∀ e ∈ C5T10.C, (C5T10.Pq d e).den ∣ C5T10_den ∧ (C5T10.Pq' d e).den ∣ C5T10_den) := by
  constructor <;> decide +kernel
#print axioms C5T10_ok
#print axioms C5T10_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
