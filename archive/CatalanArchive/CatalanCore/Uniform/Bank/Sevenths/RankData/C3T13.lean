import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type d63101b32bfccde707e7b08208eaa96b1421673fd5253fbe1a2afe04d5b181b3, root class 3. -/
def C3T13 : FibreCert where
  R := {0, 1, 2, 3, 4}
  C := {0, 1, 2, 3, 4}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 5) | 2 => (-29 / 60) | 3 => (-197 / 380) | 4 => (-664 / 1235) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24 / 25) | 2 => (-3781 / 3600) | 3 => (-465647 / 433200) | 4 => (-9928171 / 9151350) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | 4, 4 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T13_ok : C3T13.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T13_den : ℕ := 1
theorem C3T13_den_ok :
    (∀ d ∈ C3T13.R, ∀ e ∈ C3T13.R, (C3T13.Lq d e).den ∣ C3T13_den ∧ (C3T13.Lq' d e).den ∣ C3T13_den) ∧
    (∀ d ∈ C3T13.C, ∀ e ∈ C3T13.C, (C3T13.Pq d e).den ∣ C3T13_den ∧ (C3T13.Pq' d e).den ∣ C3T13_den) := by
  constructor <;> decide +kernel
#print axioms C3T13_ok
#print axioms C3T13_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
