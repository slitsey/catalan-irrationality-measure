import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type b2c1f075c43314c34a322f9a84a2c17225133a852449df8881a61e389142d7c0, root class 9. -/
def C9T19 : FibreCert where
  R := {0, 1, 2, 3}
  C := {0, 1, 2, 3}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | 2 => (-39 / 44) | 3 => (-373 / 396) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | 2 => (-4293 / 1936) | 3 => (-354025 / 156816) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | 3, 3 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T19_ok : C9T19.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T19_den : ℕ := 1
theorem C9T19_den_ok :
    (∀ d ∈ C9T19.R, ∀ e ∈ C9T19.R, (C9T19.Lq d e).den ∣ C9T19_den ∧ (C9T19.Lq' d e).den ∣ C9T19_den) ∧
    (∀ d ∈ C9T19.C, ∀ e ∈ C9T19.C, (C9T19.Pq d e).den ∣ C9T19_den ∧ (C9T19.Pq' d e).den ∣ C9T19_den) := by
  constructor <;> decide +kernel
#print axioms C9T19_ok
#print axioms C9T19_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
