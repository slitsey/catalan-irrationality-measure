import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 20a5fe8f6f26580e4f0722a74c04c10c850485ff8f3bcb8bb6cc5effd5074814, root class 13. -/
def C13T36 : FibreCert where
  R := {0}
  C := ∅
  lf := fun d => match d with | 0 => (-7 / 6) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 36) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq := fun _ _ => 0
  Pq' := fun _ _ => 0
  kr := {0}
  kc := ∅

theorem C13T36_ok : C13T36.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C13T36_den : ℕ := 1
theorem C13T36_den_ok :
    (∀ d ∈ C13T36.R, ∀ e ∈ C13T36.R, (C13T36.Lq d e).den ∣ C13T36_den ∧ (C13T36.Lq' d e).den ∣ C13T36_den) ∧
    (∀ d ∈ C13T36.C, ∀ e ∈ C13T36.C, (C13T36.Pq d e).den ∣ C13T36_den ∧ (C13T36.Pq' d e).den ∣ C13T36_den) := by
  constructor <;> decide +kernel
theorem C13T36_rload_0 : C13T36.rload 0 = (1, (-7 / 6)) := by decide +kernel
#print axioms C13T36_ok
#print axioms C13T36_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
