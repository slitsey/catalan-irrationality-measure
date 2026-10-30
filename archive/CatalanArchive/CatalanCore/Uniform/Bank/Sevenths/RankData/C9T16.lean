import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type b482f89e99427f00d6dad6ef624b43a8fd1396d369ae4d579fa0a2a09d4ae999, root class 9. -/
def C9T16 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-7 / 4) | 1 => (-61 / 44) | 2 => (-505 / 396) | 3 => (-12097 / 9900) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | 1 => (-4777 / 1936) | 2 => (-371449 / 156816) | 3 => (-228949609 / 98010000) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T16_ok : C9T16.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T16_den : ℕ := 1
theorem C9T16_den_ok :
    (∀ d ∈ C9T16.R, ∀ e ∈ C9T16.R, (C9T16.Lq d e).den ∣ C9T16_den ∧ (C9T16.Lq' d e).den ∣ C9T16_den) ∧
    (∀ d ∈ C9T16.C, ∀ e ∈ C9T16.C, (C9T16.Pq d e).den ∣ C9T16_den ∧ (C9T16.Pq' d e).den ∣ C9T16_den) := by
  constructor <;> decide +kernel
#print axioms C9T16_ok
#print axioms C9T16_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
