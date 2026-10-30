import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type fd57398b70a382f62010fa8d1fa2afcdf4d4b4169e5dfcb3bafe5998ac1ed46d, root class 3. -/
def C3T22 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-4 / 3) | 1 => (-19 / 21) | _ => 0
  ee := fun d => match d with | 0 => (-16 / 9) | 1 => (-487 / 441) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T22_ok : C3T22.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T22_den : ℕ := 1
theorem C3T22_den_ok :
    (∀ d ∈ C3T22.R, ∀ e ∈ C3T22.R, (C3T22.Lq d e).den ∣ C3T22_den ∧ (C3T22.Lq' d e).den ∣ C3T22_den) ∧
    (∀ d ∈ C3T22.C, ∀ e ∈ C3T22.C, (C3T22.Pq d e).den ∣ C3T22_den ∧ (C3T22.Pq' d e).den ∣ C3T22_den) := by
  constructor <;> decide +kernel
#print axioms C3T22_ok
#print axioms C3T22_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
