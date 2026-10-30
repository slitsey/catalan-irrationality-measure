import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type eb27247b368e29f96fc1c09f0d29bc27307c73d367757612e05adf111541ea42, root class 11. -/
def C11T07 : FibreCert where
  R := {0, 1, 2, 3, 4, 5}
  C := {0, 1, 2, 3, 4, 5}
  lf := fun d => match d with | 0 => 0 | 1 => (-5 / 2) | 2 => (-25 / 9) | 3 => (-415 / 144) | 4 => (-9725 / 3312) | 5 => (-49177 / 16560) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-45 / 4) | 2 => (-940 / 81) | 3 => (-242305 / 20736) | 4 => (-128509825 / 10969344) | 5 => (-3216706777 / 274233600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | 5, 5 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C11T07_ok : C11T07.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T07_den : ℕ := 1
theorem C11T07_den_ok :
    (∀ d ∈ C11T07.R, ∀ e ∈ C11T07.R, (C11T07.Lq d e).den ∣ C11T07_den ∧ (C11T07.Lq' d e).den ∣ C11T07_den) ∧
    (∀ d ∈ C11T07.C, ∀ e ∈ C11T07.C, (C11T07.Pq d e).den ∣ C11T07_den ∧ (C11T07.Pq' d e).den ∣ C11T07_den) := by
  constructor <;> decide +kernel
#print axioms C11T07_ok
#print axioms C11T07_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
