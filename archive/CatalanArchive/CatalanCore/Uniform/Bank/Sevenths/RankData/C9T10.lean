import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 9c1409d078a029d1c51f4f73ef64adf6e27578b68d53bd6bc3eca19ba307420e, root class 9. -/
def C9T10 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => (-7 / 4) | 1 => (-61 / 44) | 2 => (-505 / 396) | 3 => (-12097 / 9900) | 4 => (-94301 / 79200) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | 1 => (-4777 / 1936) | 2 => (-371449 / 156816) | 3 => (-228949609 / 98010000) | 4 => (-14560890601 / 6272640000) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T10_ok : C9T10.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T10_den : ℕ := 1
theorem C9T10_den_ok :
    (∀ d ∈ C9T10.R, ∀ e ∈ C9T10.R, (C9T10.Lq d e).den ∣ C9T10_den ∧ (C9T10.Lq' d e).den ∣ C9T10_den) ∧
    (∀ d ∈ C9T10.C, ∀ e ∈ C9T10.C, (C9T10.Pq d e).den ∣ C9T10_den ∧ (C9T10.Pq' d e).den ∣ C9T10_den) := by
  constructor <;> decide +kernel
#print axioms C9T10_ok
#print axioms C9T10_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
