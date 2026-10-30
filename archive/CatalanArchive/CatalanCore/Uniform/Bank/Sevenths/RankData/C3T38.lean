import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 7845a6b0310c8488eb9d89514eac0917a0c995ae7339d2ddc76e7c081c601749, root class 3. -/
def C3T38 : FibreCert where
  R := {0}
  C := ∅
  lf := fun d => match d with | 0 => 0 | _ => 0
  ee := fun d => match d with | 0 => 0 | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun _ _ => 0
  Pq' := fun _ _ => 0
  kr := {0}
  kc := ∅

theorem C3T38_ok : C3T38.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T38_den : ℕ := 1
theorem C3T38_den_ok :
    (∀ d ∈ C3T38.R, ∀ e ∈ C3T38.R, (C3T38.Lq d e).den ∣ C3T38_den ∧ (C3T38.Lq' d e).den ∣ C3T38_den) ∧
    (∀ d ∈ C3T38.C, ∀ e ∈ C3T38.C, (C3T38.Pq d e).den ∣ C3T38_den ∧ (C3T38.Pq' d e).den ∣ C3T38_den) := by
  constructor <;> decide +kernel
theorem C3T38_rload_0 : C3T38.rload 0 = (1, 0) := by decide +kernel
#print axioms C3T38_ok
#print axioms C3T38_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
