import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 2041f3f01f63255676518b5fb301ab8a242b6f31bf6e18c77bd780ca16f9d198, root class 3. -/
def C3T35 : FibreCert where
  R := {0}
  C := {0}
  lf := fun d => match d with | 0 => 0 | _ => 0
  ee := fun d => match d with | 0 => 0 | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {0}
  kc := {0}

theorem C3T35_ok : C3T35.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T35_den : ℕ := 1
theorem C3T35_den_ok :
    (∀ d ∈ C3T35.R, ∀ e ∈ C3T35.R, (C3T35.Lq d e).den ∣ C3T35_den ∧ (C3T35.Lq' d e).den ∣ C3T35_den) ∧
    (∀ d ∈ C3T35.C, ∀ e ∈ C3T35.C, (C3T35.Pq d e).den ∣ C3T35_den ∧ (C3T35.Pq' d e).den ∣ C3T35_den) := by
  constructor <;> decide +kernel
theorem C3T35_rload_0 : C3T35.rload 0 = (1, 0) := by decide +kernel
theorem C3T35_cload_0 : C3T35.cload 0 = (1, 0) := by decide +kernel
#print axioms C3T35_ok
#print axioms C3T35_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
