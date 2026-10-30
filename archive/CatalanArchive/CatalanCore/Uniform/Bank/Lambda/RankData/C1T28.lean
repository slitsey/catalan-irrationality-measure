import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type aa21b4d5219a43b5dcb61a6a200b46d6fede9f326e49f9431c715cee535d964b, root class 1. -/
def C1T28 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => 0 | 1 => (-3) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-15) | _ => 0
  Lq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C1T28_ok : C1T28.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T28_den : ℕ := 1
theorem C1T28_den_ok :
    (∀ d ∈ C1T28.R, ∀ e ∈ C1T28.R, (C1T28.Lq d e).den ∣ C1T28_den ∧ (C1T28.Lq' d e).den ∣ C1T28_den) ∧
    (∀ d ∈ C1T28.C, ∀ e ∈ C1T28.C, (C1T28.Pq d e).den ∣ C1T28_den ∧ (C1T28.Pq' d e).den ∣ C1T28_den) := by
  constructor <;> decide +kernel
theorem C1T28_rload_1 : C1T28.rload 1 = (1, 0) := by decide +kernel
#print axioms C1T28_ok
#print axioms C1T28_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
