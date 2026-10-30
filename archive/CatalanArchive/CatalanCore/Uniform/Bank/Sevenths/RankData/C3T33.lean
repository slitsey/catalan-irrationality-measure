import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type f6486255a571de42e625aac98e902741984d00adcd5de6c87b6a64a66c416c68, root class 3. -/
def C3T33 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => 0 | 1 => (-2 / 5) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-24 / 25) | _ => 0
  Lq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C3T33_ok : C3T33.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C3T33_den : ℕ := 1
theorem C3T33_den_ok :
    (∀ d ∈ C3T33.R, ∀ e ∈ C3T33.R, (C3T33.Lq d e).den ∣ C3T33_den ∧ (C3T33.Lq' d e).den ∣ C3T33_den) ∧
    (∀ d ∈ C3T33.C, ∀ e ∈ C3T33.C, (C3T33.Pq d e).den ∣ C3T33_den ∧ (C3T33.Pq' d e).den ∣ C3T33_den) := by
  constructor <;> decide +kernel
theorem C3T33_rload_1 : C3T33.rload 1 = (1, 0) := by decide +kernel
#print axioms C3T33_ok
#print axioms C3T33_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
