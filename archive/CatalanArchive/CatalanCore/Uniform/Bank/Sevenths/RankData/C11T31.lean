import CatalanCore.Uniform.Content.RankProducer.Loads
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.Sevenths.RankData
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.RankProducer
/-- Source type 408186d0e296e0c0656dc4d312fee85c261cf111dbc77e31d986fda1c33c8903, root class 11. -/
def C11T31 : FibreCert where
  R := {0, 1}
  C := {0, 1}
  lf := fun d => match d with | 0 => 0 | 1 => (-5 / 2) | _ => 0
  ee := fun d => match d with | 0 => 0 | 1 => (-45 / 4) | _ => 0
  Lq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Lq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  Pq' := fun d e => match d, e with | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
  kr := ∅
  kc := ∅

theorem C11T31_ok : C11T31.Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def C11T31_den : ℕ := 1
theorem C11T31_den_ok :
    (∀ d ∈ C11T31.R, ∀ e ∈ C11T31.R, (C11T31.Lq d e).den ∣ C11T31_den ∧ (C11T31.Lq' d e).den ∣ C11T31_den) ∧
    (∀ d ∈ C11T31.C, ∀ e ∈ C11T31.C, (C11T31.Pq d e).den ∣ C11T31_den ∧ (C11T31.Pq' d e).den ∣ C11T31_den) := by
  constructor <;> decide +kernel
#print axioms C11T31_ok
#print axioms C11T31_den_ok
end CatalanCore.Uniform.Bank.Sevenths.RankData
