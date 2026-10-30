import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type cfe3406a36a7e9ab3a78c6da3b4d108f7ac4c79fc3b0c64ae0662152f1df5964, root class 3. -/
def C3T31 : FibreCert where
  R := ∅
  C := {0}
  lf := fun d => match d with | 0 => (-4 / 3) | _ => 0
  ee := fun d => match d with | 0 => (-16 / 9) | _ => 0
  Lq := fun _ _ => 0
  Lq' := fun _ _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := ∅
  kc := {0}

theorem C3T31_ok : C3T31.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T31_den : ℕ := 1
theorem C3T31_den_ok :
    (∀ d ∈ C3T31.R, ∀ e ∈ C3T31.R, (C3T31.Lq d e).den ∣ C3T31_den ∧ (C3T31.Lq' d e).den ∣ C3T31_den) ∧
    (∀ d ∈ C3T31.C, ∀ e ∈ C3T31.C, (C3T31.Pq d e).den ∣ C3T31_den ∧ (C3T31.Pq' d e).den ∣ C3T31_den) := by
  constructor <;> decide +kernel
theorem C3T31_cload_0 : C3T31.cload 0 = (1, (-4 / 3)) := by decide +kernel
#print axioms C3T31_ok
#print axioms C3T31_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
