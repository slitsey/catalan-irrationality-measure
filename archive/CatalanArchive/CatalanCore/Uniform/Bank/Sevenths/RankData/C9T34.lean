import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type b4db523691590ad48ae005130df08d8d14de7916ce8634ba3a7d9838a90c4d3b, root class 9. -/
def C9T34 : FibreCert where
  R := {0, 1}
  C := {0}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | _ => 0
  Lq := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 1 => 1 | 1, 0 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | _, _ => 0
  kr := {1}
  kc := ∅

theorem C9T34_ok : C9T34.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T34_den : ℕ := 1
theorem C9T34_den_ok :
    (∀ d ∈ C9T34.R, ∀ e ∈ C9T34.R, (C9T34.Lq d e).den ∣ C9T34_den ∧ (C9T34.Lq' d e).den ∣ C9T34_den) ∧
    (∀ d ∈ C9T34.C, ∀ e ∈ C9T34.C, (C9T34.Pq d e).den ∣ C9T34_den ∧ (C9T34.Pq' d e).den ∣ C9T34_den) := by
  constructor <;> decide +kernel
theorem C9T34_rload_1 : C9T34.rload 1 = (1, 0) := by decide +kernel
#print axioms C9T34_ok
#print axioms C9T34_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
