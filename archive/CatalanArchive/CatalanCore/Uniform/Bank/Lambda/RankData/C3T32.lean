import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type bdbf608cd489fefe581048dce2d265cf8ac085aec65e948e791b5d80cf733150, root class 3. -/
def C3T32 : FibreCert where
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

theorem C3T32_ok : C3T32.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T32_den : ℕ := 1
theorem C3T32_den_ok :
    (∀ d ∈ C3T32.R, ∀ e ∈ C3T32.R, (C3T32.Lq d e).den ∣ C3T32_den ∧ (C3T32.Lq' d e).den ∣ C3T32_den) ∧
    (∀ d ∈ C3T32.C, ∀ e ∈ C3T32.C, (C3T32.Pq d e).den ∣ C3T32_den ∧ (C3T32.Pq' d e).den ∣ C3T32_den) := by
  constructor <;> decide +kernel
theorem C3T32_rload_0 : C3T32.rload 0 = (1, 0) := by decide +kernel
#print axioms C3T32_ok
#print axioms C3T32_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
