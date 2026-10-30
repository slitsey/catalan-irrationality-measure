import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 53e03358e86b9c4cee3ca849bc19f36d87551984d49d9f26498cd68335d0a8c0, root class 11. -/
def C11T10 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-7 / 2) | 1 => (-59 / 18) | 2 => (-463 / 144) | 3 => (-10553 / 3312) | 4 => (-52489 / 16560) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 4) | 1 => (-3841 / 324) | 2 => (-244609 / 20736) | 3 => (-129195409 / 10969344) | 4 => (-3227676121 / 274233600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C11T10_ok : C11T10.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T10_den : ℕ := 1
theorem C11T10_den_ok :
    (∀ d ∈ C11T10.R, ∀ e ∈ C11T10.R, (C11T10.Lq d e).den ∣ C11T10_den ∧ (C11T10.Lq' d e).den ∣ C11T10_den) ∧
    (∀ d ∈ C11T10.C, ∀ e ∈ C11T10.C, (C11T10.Pq d e).den ∣ C11T10_den ∧ (C11T10.Pq' d e).den ∣ C11T10_den) := by
  constructor <;> decide +kernel
#print axioms C11T10_ok
#print axioms C11T10_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
