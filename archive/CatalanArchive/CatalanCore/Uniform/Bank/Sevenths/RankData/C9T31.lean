import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 3216fa0430fd66ab33f7528955634b04056ddf827f28a5e8a07cfe09b839047c, root class 9. -/
def C9T31 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => (-7 / 4) | 1 => (-61 / 44) | _ => 0
  ee := fun d => match d with | 0 => (-49 / 16) | 1 => (-4777 / 1936) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (-64 / 539) | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 0 => (64 / 539) | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C9T31_ok : C9T31.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T31_den : ℕ := 539
theorem C9T31_den_ok :
    (∀ d ∈ C9T31.R, ∀ e ∈ C9T31.R, (C9T31.Lq d e).den ∣ C9T31_den ∧ (C9T31.Lq' d e).den ∣ C9T31_den) ∧
    (∀ d ∈ C9T31.C, ∀ e ∈ C9T31.C, (C9T31.Pq d e).den ∣ C9T31_den ∧ (C9T31.Pq' d e).den ∣ C9T31_den) := by
  constructor <;> decide +kernel
theorem C9T31_rload_1 : C9T31.rload 1 = ((475 / 539), (-33 / 28)) := by decide +kernel
#print axioms C9T31_ok
#print axioms C9T31_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
