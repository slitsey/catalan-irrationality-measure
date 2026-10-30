import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 0c21c0b98e036ebb60440bd9e779aab83f3593e0b3b4035f6b6627a617b03e84, root class 3. -/
def C3T13 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-1 / 3) | 2 => (-17 / 42) | 3 => (-67 / 154) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-7 / 9) | 2 => (-1507 / 1764) | 3 => (-62285 / 71148) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
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
end CatalanCore.Uniform.Bank.Lambda.RankData
