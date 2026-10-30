import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 6d6185c7f1100b3183c3f5179a9f11c11c9673942d18171b5fbaa7846ea702e0, root class 3. -/
def C3T16 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => (-7 / 5) | 1 => (-59 / 60) | 2 => (-971 / 1140) | 3 => (-3891 / 4940) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 25) | 1 => (-4681 / 3600) | 2 => (-1541341 / 1299600) | 3 => (-84001043 / 73210800) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T16_ok : C3T16.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T16_den : ℕ := 1
theorem C3T16_den_ok :
    (∀ d ∈ C3T16.R, ∀ e ∈ C3T16.R, (C3T16.Lq d e).den ∣ C3T16_den ∧ (C3T16.Lq' d e).den ∣ C3T16_den) ∧
    (∀ d ∈ C3T16.C, ∀ e ∈ C3T16.C, (C3T16.Pq d e).den ∣ C3T16_den ∧ (C3T16.Pq' d e).den ∣ C3T16_den) := by
  constructor <;> decide +kernel
#print axioms C3T16_ok
#print axioms C3T16_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
