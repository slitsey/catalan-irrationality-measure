import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 4ca29d910fbc36f88495d9d820a9faa0a7f21a6d9a6ca87c67bb79730c349a74, root class 3. -/
def C3T23 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 5) | 2 => (-29 / 60) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24 / 25) | 2 => (-3781 / 3600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T23_ok : C3T23.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T23_den : ℕ := 1
theorem C3T23_den_ok :
    (∀ d ∈ C3T23.R, ∀ e ∈ C3T23.R, (C3T23.Lq d e).den ∣ C3T23_den ∧ (C3T23.Lq' d e).den ∣ C3T23_den) ∧
    (∀ d ∈ C3T23.C, ∀ e ∈ C3T23.C, (C3T23.Pq d e).den ∣ C3T23_den ∧ (C3T23.Pq' d e).den ∣ C3T23_den) := by
  constructor <;> decide +kernel
#print axioms C3T23_ok
#print axioms C3T23_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
