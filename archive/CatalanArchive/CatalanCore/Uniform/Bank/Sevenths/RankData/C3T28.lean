import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 3fcb6c1a080817708a04f0f5654e1aee6396ae09e5d6470ec2d0f55093d7b34e, root class 3. -/
def C3T28 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => (-7 / 5) | 1 => (-59 / 60) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 25) | 1 => (-4681 / 3600) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C3T28_ok : C3T28.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T28_den : ℕ := 1
theorem C3T28_den_ok :
    (∀ d ∈ C3T28.R, ∀ e ∈ C3T28.R, (C3T28.Lq d e).den ∣ C3T28_den ∧ (C3T28.Lq' d e).den ∣ C3T28_den) ∧
    (∀ d ∈ C3T28.C, ∀ e ∈ C3T28.C, (C3T28.Pq d e).den ∣ C3T28_den ∧ (C3T28.Pq' d e).den ∣ C3T28_den) := by
  constructor <;> decide +kernel
#print axioms C3T28_ok
#print axioms C3T28_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
