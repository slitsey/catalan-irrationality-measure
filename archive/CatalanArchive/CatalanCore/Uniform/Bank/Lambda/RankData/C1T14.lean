import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Lambda.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type fb7e66a8bd6a2472687530361fa73cdcc08e5344c4d80f6ea85154d42bbfe430, root class 1. -/
def C1T14 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => (-4) | 1 => (-19 / 5) | 2 => (-337 / 90) | _ => 0
  ee := fun d => match d with | 0 => (-16) | 1 => (-391 / 25) | 2 => (-126259 / 8100) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C1T14_ok : C1T14.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C1T14_den : ℕ := 1
theorem C1T14_den_ok :
    (∀ d ∈ C1T14.R, ∀ e ∈ C1T14.R, (C1T14.Lq d e).den ∣ C1T14_den ∧ (C1T14.Lq' d e).den ∣ C1T14_den) ∧
    (∀ d ∈ C1T14.C, ∀ e ∈ C1T14.C, (C1T14.Pq d e).den ∣ C1T14_den ∧ (C1T14.Pq' d e).den ∣ C1T14_den) := by
  constructor <;> decide +kernel
#print axioms C1T14_ok
#print axioms C1T14_den_ok
end CatalanCore.Uniform.Bank.Lambda.RankData
