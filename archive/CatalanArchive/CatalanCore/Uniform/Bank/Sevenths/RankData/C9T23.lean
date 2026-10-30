import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type f571658b6e4e0389977914cd8391ccd43bcbce1c19549a5b493f0276b2c79590, root class 9. -/
def C9T23 : FibreCert where
  R := {0, 1, 2}
  C := {0, 1, 2}
  lf := fun d => match d with | 0 => 0 | 1 => (-3 / 4) | 2 => (-39 / 44) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-33 / 16) | 2 => (-4293 / 1936) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C9T23_ok : C9T23.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C9T23_den : ℕ := 1
theorem C9T23_den_ok :
    (∀ d ∈ C9T23.R, ∀ e ∈ C9T23.R, (C9T23.Lq d e).den ∣ C9T23_den ∧ (C9T23.Lq' d e).den ∣ C9T23_den) ∧
    (∀ d ∈ C9T23.C, ∀ e ∈ C9T23.C, (C9T23.Pq d e).den ∣ C9T23_den ∧ (C9T23.Pq' d e).den ∣ C9T23_den) := by
  constructor <;> decide +kernel
#print axioms C9T23_ok
#print axioms C9T23_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
