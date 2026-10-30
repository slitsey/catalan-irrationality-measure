import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 9724f2ac894b3a95877ba0aae2e1f7a82c484b4d26fbd2599336c26f0c4e961e, root class 9. -/
def C9T04 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => (-7 / 4) | 1 => (-61 / 44) | 2 => (-505 / 396) | 3 => (-12097 / 9900) | 4 => (-94301 / 79200) | 5 => (-1204793 / 1029600) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | 1 => (-4777 / 1936) | 2 => (-371449 / 156816) | 3 => (-228949609 / 98010000) | 4 => (-14560890601 / 6272640000) | 5 => (-2452538505169 / 1060076160000) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T04_ok : C9T04.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T04_den : ℕ := 1
theorem C9T04_den_ok :
    (∀ d ∈ C9T04.R, ∀ e ∈ C9T04.R, (C9T04.Lq d e).den ∣ C9T04_den ∧ (C9T04.Lq' d e).den ∣ C9T04_den) ∧
    (∀ d ∈ C9T04.C, ∀ e ∈ C9T04.C, (C9T04.Pq d e).den ∣ C9T04_den ∧ (C9T04.Pq' d e).den ∣ C9T04_den) := by
  constructor <;> decide +kernel
#print axioms C9T04_ok
#print axioms C9T04_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
