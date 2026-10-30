import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 7006dd3b2a0545fd901c6f7e3b052605b9a07f2e505a69a1822834ef4da7813b, root class 11. -/
def C11T16 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-7 / 2) | 1 => (-59 / 18) | 2 => (-463 / 144) | 3 => (-10553 / 3312) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 4) | 1 => (-3841 / 324) | 2 => (-244609 / 20736) | 3 => (-129195409 / 10969344) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C11T16_ok : C11T16.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T16_den : ℕ := 1
theorem C11T16_den_ok :
    (∀ d ∈ C11T16.R, ∀ e ∈ C11T16.R, (C11T16.Lq d e).den ∣ C11T16_den ∧ (C11T16.Lq' d e).den ∣ C11T16_den) ∧
    (∀ d ∈ C11T16.C, ∀ e ∈ C11T16.C, (C11T16.Pq d e).den ∣ C11T16_den ∧ (C11T16.Pq' d e).den ∣ C11T16_den) := by
  constructor <;> decide +kernel
#print axioms C11T16_ok
#print axioms C11T16_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
